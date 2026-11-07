-- Prove2me | Theorems.Thm_MeanBudgetXC_section_3_6_open_bounded
-- name    : MeanBudgetXC.section_3_6_open_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:30.376093+00:00
-- url     : https://prove2.me/theorems/9605e339-5f06-4b88-8a18-494b981f2d27
-- title:
--   Section 3.6 — an open set in $P_B$, dimension $M$ and boundedness
-- statement:
--   Let $3\le d\le N$ and $0<B\le2$.
--
--   1. For every $t$ with $0<t<\min\{B/(N(d-1)),\ 1/\binom d2\}$, the constant array $q_{ij}=t$ is an interior point of $P_B$ in $\mathbb{R}^M$.
--   2. Thus $\dim P_B=M$.
--   3. Star averaging gives $W(q)=\sum_{i<j}q_{ij}\le B(N-1)/(2(d-1))$ throughout $P_B$.
--   4. The body $P_B$ is closed and bounded.
--
--   With the dimension bound of Appendix A.4, these facts give the lower bound $M+1\le\mathrm{xc}(P_B)$.
--
--   **Formalization Note** The dimension of $P_B$ is the `finrank` of its vector span, the dimension of its affine hull.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
--   - encoding: $\dim P_B=M$ → the finrank of the vector span of $P_B$ equals the number of pair coordinates; reason: this is the dimension of the affine hull
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.6, p.17

import Mathlib
import Definitions.Def_MeanBudgetXC_budgetBody

namespace MeanBudgetXC

/-- **Section 3.6, open set and boundedness** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition
for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 3.6,
p.17). Let `3 ≤ d ≤ N` and `0 < B ≤ 2`. For every `t` with
`0 < t < min{B/(N(d − 1)), 1/(d choose 2)}`, the constant array `q_ij = t` is an interior point of
`P_B`; thus `dim P_B = M`. Star averaging gives `W(q) = ∑_{i<j} q_ij ≤ B(N − 1)/(2(d − 1))`
throughout `P_B`, and the closed nonnegative body `P_B` is bounded.

**Formalization Note** `dim P_B` is the dimension of the affine hull, the `finrank` of the vector
span; `M = card (Pair V)`. The vertex set is a generic finite type `V` with `N = card V`. -/
theorem section_3_6_open_bounded {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd3 : 3 ≤ d)
    (hdN : d ≤ Fintype.card V) (B : ℝ) (hB0 : 0 < B) (hB2 : B ≤ 2) :
    (∀ t : ℝ, 0 < t → t < B / ((Fintype.card V : ℝ) * ((d : ℝ) - 1)) →
        t < 1 / (d.choose 2 : ℝ) → (fun _ => t) ∈ interior (budgetBody V d 2 B)) ∧
      Module.finrank ℝ (vectorSpan ℝ (budgetBody V d 2 B)) = Fintype.card (Pair V) ∧
      (∀ q ∈ budgetBody V d 2 B,
        ∑ e, q e ≤ B * ((Fintype.card V : ℝ) - 1) / (2 * ((d : ℝ) - 1))) ∧
      IsClosed (budgetBody V d 2 B) ∧ Bornology.IsBounded (budgetBody V d 2 B) := by sorry

end MeanBudgetXC
