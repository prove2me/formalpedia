-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_4_2
-- name    : MatMulTimeLP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:27.709207+00:00
-- url     : https://prove2.me/theorems/f922fd96-015c-4675-9e1b-d9cfffa9544d
-- title:
--   Lemma 4.2, mathematical content (its work clause: `proof_lemma_4_2_projections`, `theorem_2_2`)
-- statement:
--   Let $A\in\mathbb R^{d\times n}$, $b,c$, with $n\ge 100$, and let $(x,y,s)$ be strictly feasible: $Ax=b$, $A^\top y+s=c$, $x,s>0$, with $0.98\tau\le x_is_i\le\tau$ for every $i$ and some $\tau>0$. Let $\tau'=0.9\tau$, $X=\mathrm{diag}(x)$, $P$ the orthogonal projection onto $\mathrm{im}(XA^\top)$, $Q=I-P$, $H=Q-P$ and $h=-2Q(x\circ s/\tau'-\mathbf 1)$. Then:
--
--   1. $\|H\|_2=1$, $\|h\|_2\le n$, and $a=Hf(a)+h$ has a solution with $\|a\|_1\le n$, which is unique in $\mathbb R^n$.
--   2. For every $\hat a$ with $\|Hf(\hat a)+h-\hat a\|_2\le n^{-5}$ and $\|\hat a\|_2\le 512n$, let $r$ be its residual, $\xi'=\hat\xi+\tfrac12Pr$ and $\sigma'=\hat\sigma-\tfrac12Qr$. There is $\lambda$ with $\sigma'-x\circ s/\tau'=(AX)^\top\lambda$, and for every such $\lambda$ the point
--
--   $$x^+=X\xi',\qquad y^+=y-\tau'\lambda,\qquad s^+=\tau'X^{-1}\sigma'$$
--
--   is strictly feasible, with $0.98\tau^+\le x_i^+s_i^+\le\tau^+$ for every $i$, where $\tau^+=0.909\tau$.
--
--   One round of the long-step interior point method therefore shrinks the path parameter by a constant factor. Item 1 is exactly the hypothesis of Theorem 2.2, and item 2 uses only its guarantee.
--
--   Differences from the source:
--   - encoding: "using one oracle call to Theorem 2.2 and $O((d+n)^{\omega+o(1)})$ additional work, we can find" the point → the mathematical conjunction of items 1 and 2 here, with the work in the milestone `proof_lemma_4_2_projections` and the oracle in `theorem_2_2`; reason: composing the three items gives the page statement; the machine appears only in those two
--   - reading: "we can find" a strictly feasible point → the explicit recovery formulas of pp.19–20, for every admissible $\hat a$ and $\lambda$; reason: these are the constructions the proof uses, stated in the strength the composition needs
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma 4.2, p.16, proved pp.17–21

import Mathlib
import Definitions.Def_MatMulTimeLP_FixPoint

open scoped Matrix.Norms.L2Operator

namespace MatMulTimeLP

open Matrix WrightPDIPM.CentralPath

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma 4.2, pp.16–21, mathematical content. For a strictly
feasible point with `0.98τ ≤ xᵢsᵢ ≤ τ`, `τ' = 0.9τ` and `P` the orthogonal projection onto `im(XAᵀ)`:
(a) `H = Q - P`, `h = -2Q(x∘s/τ' - 1)` meet the hypotheses of Theorem 2.2, with a solution of `a = Hf(a) + h`,
unique in `ℝⁿ`, with `‖a‖₁ ≤ n`; (b) every `â` with `‖Hf(â) + h - â‖₂ ≤ n⁻⁵`, `‖â‖₂ ≤ 512n` recovers a strictly
feasible `(x⁺, y⁺, s⁺)` with `0.98τ⁺ ≤ x⁺ᵢs⁺ᵢ ≤ τ⁺`, `τ⁺ = 0.909τ`.

**Formalization Note** "One oracle call and `O((d+n)^(ω+o(1)))` additional work" is the composition of (a), (b)
with `proof_lemma_4_2_projections` and `theorem_2_2`, the mission's two machine statements. There is no rank
hypothesis, as on the page. -/
theorem lemma_4_2 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ)
    (hn : 100 ≤ n) (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ) (hpt : (x, y, s) ∈ Fo A b c)
    (τ : ℝ) (hτ : 0 < τ) (hxs : ∀ i, 0.98 * τ ≤ x i * s i ∧ x i * s i ≤ τ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthoProjOnto P (diagonal x * Aᵀ)) :
    (‖ipmH P‖ = 1 ∧ l2Norm (ipmh P x s (0.9 * τ)) ≤ n ∧
      ∃ a, IsFixPoint (ipmH P) (ipmh P x s (0.9 * τ)) a ∧ l1Norm a ≤ n ∧
        ∀ a', IsFixPoint (ipmH P) (ipmh P x s (0.9 * τ)) a' → a' = a) ∧
    ∀ ah : Fin n → ℝ,
      l2Norm (residual (ipmH P) (ipmh P x s (0.9 * τ)) ah) ≤ 1 / (n : ℝ) ^ 5 → l2Norm ah ≤ 512 * n →
      let r := residual (ipmH P) (ipmh P x s (0.9 * τ)) ah
      let ξ' := xiHat ah + (1 / 2 : ℝ) • (P *ᵥ r)
      let σ' := sigmaHat ah - (1 / 2 : ℝ) • ((1 - P) *ᵥ r)
      let d' : Fin n → ℝ := fun i => σ' i - x i * s i / (0.9 * τ)
      (∃ lam : Fin d → ℝ, d' = (diagonal x * Aᵀ) *ᵥ lam) ∧
      ∀ lam : Fin d → ℝ, d' = (diagonal x * Aᵀ) *ᵥ lam →
        let xp : Fin n → ℝ := fun i => x i * ξ' i
        let sp : Fin n → ℝ := fun i => 0.9 * τ * σ' i / x i
        (xp, y - (0.9 * τ) • lam, sp) ∈ Fo A b c ∧
          ∀ i, 0.98 * (0.909 * τ) ≤ xp i * sp i ∧ xp i * sp i ≤ 0.909 * τ := by sorry

end MatMulTimeLP
