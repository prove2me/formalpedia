-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_B_1
-- name    : MatMulTimeLP.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:49.510738+00:00
-- url     : https://prove2.me/theorems/9628bf5c-b550-491e-a6b9-333126cdbab2
-- title:
--   Lemma B.1 (items 1–2 and the rank sentence) — the auxiliary LP, its explicit start, recovery from gap $\delta^2$
-- statement:
--   Let $A\in\mathbb R^{d\times n}$, $b\in\mathbb R^d$, $c\in\mathbb R^n$. Suppose $\{x\ge 0:Ax=b\}$ is nonempty and every feasible point satisfies $\|x\|_\infty\le R$, for a given $R>0$. Let $C>0$ with $\|c\|_\infty\le C$, let $0<\delta\le 1/100$, and let $(\tilde A,\tilde b,\tilde c)$ be the auxiliary LP. Then:
--
--   1. $(\tilde x^{(0)},\tilde y^{(0)},\tilde s^{(0)})=(\mathbf 1,(0,-1),(\mathbf 1+\delta c/C,1,1))$ is strictly feasible, and for every $i$, $1-\delta\le\tilde x^{(0)}_i\tilde s^{(0)}_i\le 1+\delta$ and, with $\tau_0=1+\delta$, $0.98\tau_0\le\tilde x^{(0)}_i\tilde s^{(0)}_i\le\tau_0$.
--   2. If $(\tilde x,\tilde y,\tilde s)$ is feasible for the auxiliary LP with $\tilde x^\top\tilde s\le\delta^2$, then $\hat x=R\tilde x_{1:n}$ satisfies $\hat x\ge 0$ and
--
--   $$c^\top\hat x\le\min_{Ax=b,\,x\ge 0}c^\top x+\delta RC,\qquad \|A\hat x-b\|_1\le 4n\delta\Bigl(R\sum_{i,j}|A_{ij}|+\|b\|_1\Bigr).$$
--
--   3. If $A$ has full row rank, so does $\tilde A$.
--
--   This is the initialization of the interior point method. The lemma's last sentence, on the sparse construction time, is not stated here: the goal's input is dense, and the construction is explicit inside the machine of Theorem 4.1.
--
--   **Formalization Note** Since $\tilde x^{(0)}=\mathbf 1$, the products $\tilde x^{(0)}_i\tilde s^{(0)}_i$ are written $\tilde s^{(0)}_i$.
--
--   Differences from the source:
--   - encoding: block matrices with $n+2$ columns and $d+1$ rows → `Fin.snoc` blocks on `Fin (n + 2)`, `Fin (d + 1)`; reason: Lean indexing; same matrix
--   - encoding: $\min_{Ax=b,x\ge 0}c^\top x$ → `∀ x'` feasible, `c ⬝ᵥ x̂ ≤ c ⬝ᵥ x' + δRC`; reason: the feasible set is nonempty and compact, so the two agree
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma B.1, pp.48–49

import Mathlib
import Definitions.Def_MatMulTimeLP_LP

namespace MatMulTimeLP

open Matrix WrightPDIPM.CentralPath

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma B.1, items 1–2 and the rank sentence, pp.48–49.
The auxiliary LP has an explicit strictly feasible point with `0.98τ₀ ≤ x̃⁽⁰⁾ᵢ s̃⁽⁰⁾ᵢ ≤ τ₀`, `τ₀ = 1 + δ`; a
feasible primal–dual point of gap at most `δ²` recovers an approximate solution of the original LP; and
`Ã` inherits full row rank.

**Formalization Note** The blocks of `Ã` use `Fin.snoc`; `min` is written `∀ x'` over the feasible set
(which is nonempty and compact). Since `x̃⁽⁰⁾ = 1`, the products `x̃⁽⁰⁾ᵢ s̃⁽⁰⁾ᵢ` are written `s̃⁽⁰⁾ᵢ`. The lemma's
sparse-time sentence (p.49) is not stated here. -/
theorem lemma_B_1 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ)
    (R C δ : ℝ) (hfeas : ∃ x, PrimalFeasible A b x) (hR : 0 < R)
    (hbound : ∀ x, PrimalFeasible A b x → ∀ j, |x j| ≤ R) (hC : 0 < C) (hc : ‖c‖ ≤ C)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 100) :
    ((fun _ => 1, auxY0 d, auxS0 c C δ) ∈ Fo (auxA A b R) (auxB n b R) (auxC c C δ) ∧
      (∀ i, 1 - δ ≤ auxS0 c C δ i ∧ auxS0 c C δ i ≤ 1 + δ) ∧
      (∀ i, 0.98 * (1 + δ) ≤ auxS0 c C δ i ∧ auxS0 c C δ i ≤ 1 + δ)) ∧
    (∀ xt yt st, (xt, yt, st) ∈ F (auxA A b R) (auxB n b R) (auxC c C δ) → xt ⬝ᵥ st ≤ δ ^ 2 →
      (∀ j, 0 ≤ R * firstCoords xt j) ∧
      (∀ x', PrimalFeasible A b x' →
        c ⬝ᵥ (fun j => R * firstCoords xt j) ≤ c ⬝ᵥ x' + δ * R * C) ∧
      l1Norm (A *ᵥ (fun j => R * firstCoords xt j) - b) ≤
        4 * (n : ℝ) * δ * (R * ∑ i, ∑ j, |A i j| + l1Norm b)) ∧
    (A.rank = d → (auxA A b R).rank = d + 1) := by sorry

end MatMulTimeLP
