-- Prove2me | Theorems.Thm_MatroidEquitability_Supplement_theorem_15
-- name    : MatroidEquitability.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:26:29.024957+00:00
-- url     : https://prove2.me/theorems/74c323cd-2456-4a33-a855-a9cc8eb17c6d
-- title:
--   Theorem 15 — $O(\log n)$ prefix discrepancy for cost-bounded matroid bases
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $M=([n],\mathcal I)$ be a matroid with rank function $r$, let $w\in\mathbb R^n_{\ge0}$ be weights and $c\in\mathbb R^n_{\ge0}$ costs, and let $x$ be a point of the base polytope
--   $$P(M)=\{x\in\mathbb R^n_{\ge0}: x(S)\le r(S)\ \text{for all } S\subseteq[n],\ x([n])=r([n])\}.$$
--   Then there is a basis $B$ of $M$ with $c(B)\le c^\top x$ and
--   $$\Bigl|\sum_{i=1}^t w_i\,\mathbf 1\{i\in B\}-\sum_{i=1}^t w_ix_i\Bigr|\le C\cdot\log n\cdot\max_{e\in[n]}w_e\qquad\text{for all } t\in[n].$$
--
--   This is the paper's $O(\log n)$ bound towards the cost-augmented prefix-constrained bases conjecture (Conjecture 6), which asks for a constant in place of $C\log n$. Both guarantees hold for one and the same basis.
--
--   **Formalization Note** The ground set $[n]$ is `Fin n` with $M.E$ the whole type; the paper's element $i$ is the element of value $i-1$, so the prefix $\{1,\dots,t\}$ is the set of elements of value below $t$. $P(M)$ is the platform's `OnlineCRS.Matroid.basePolytope`, $c(B)$ is `setWeight c B` and $\max_{e\in[n]}w_e$ is `maxWeight M w`. The logarithm is natural.
--
--   Differences from the source:
--   - reading: $O(\log n)\cdot\max_e w_e$ → $C\cdot\log n\cdot\max_e w_e$ with one constant $C>0$ chosen before $n, M, w, c, x$; reason: the standard meaning of $O(\cdot)$ here, and what the proof supplies (at most $3\max_e w_e$ per iteration, at most $\lfloor\log_{6/5}n\rfloor+1$ iterations). The bound is required for every $n$, including $n=1$, where $\log 1=0$ and $P(M)$ is a single integral point. For $n\ge2$, $\log n\ge\log2$, so a bound for large $n$ extends to all $n\ge2$ by enlarging $C$; the reading is no stronger than the paper's.
--   - encoding: ground set $[n]$ → `Fin n` with `M.E = univ`, element $i$ ↦ value $i-1$; reason: Lean convention, same instances.
--   - encoding: $P(M)$ → `OnlineCRS.Matroid.basePolytope M`, rank as $(\mathrm{eRk}\,S)$ read as a natural number; reason: the rank of a matroid on a finite type is finite, so this is the paper's polytope.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 15, p.18 (PDF p.20); P(M), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_maxWeight
import Definitions.Def_OnlineCRS_Matroid_Polytope

namespace MatroidEquitability

namespace Supplement

/-- **Theorem 15** (printed p.18 = PDF p.20 of Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and
Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)): `O(log n)`
prefix-constrained bases. There is a universal constant `C > 0` such that for every matroid
`M = ([n], I)`, weights `w ∈ ℝ^n_{≥0}`, costs `c ∈ ℝ^n_{≥0}` and `x ∈ P(M)`, some basis `B` of `M` has
`c(B) ≤ c⊤x` and `|Σ_{i=1}^t w_i 1{i ∈ B} − Σ_{i=1}^t w_i x_i| ≤ C · log n · max_{e∈[n]} w_e` for all
`t ∈ [n]`.

**Formalization Note.** The ground set `[n]` is `Fin n` with `M.E = univ`; the paper's element `i` is the
element of value `i − 1`, so the prefix `{1, …, t}` is `{i : i.val < t}`. `P(M)` is the platform's
`OnlineCRS.Matroid.basePolytope` (`x ≥ 0`, `x(S) ≤ r(S)` for all `S`, `x(E) = r(E)`). `O(log n)` is read
as one constant `C` chosen before `n, M, w, c, x`; `log` is the natural logarithm (the base only
rescales `C`). `c(B)` is `setWeight c B` and `max_{e∈[n]} w_e` is `maxWeight M w`. -/
theorem theorem_15 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
      ∀ (w c x : Fin n → ℝ), (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ c i) →
        x ∈ OnlineCRS.Matroid.basePolytope M →
        ∃ B : Set (Fin n), M.IsBase B ∧ setWeight c B ≤ ∑ i, c i * x i ∧
          ∀ t : ℕ, 1 ≤ t → t ≤ n →
            |∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < t), w i * B.indicator 1 i -
                ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < t), w i * x i| ≤
              C * Real.log n * maxWeight M w := by sorry

end Supplement

end MatroidEquitability
