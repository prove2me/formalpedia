-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_Supplement_construction_threshold
-- name    : MajorityDepthThree.Exact.Supplement.construction_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:16:44.650117+00:00
-- url     : https://prove2.me/theorems/34aaf7c6-c441-4f15-93ec-1e9b8c47ba72
-- title:
--   Fact 3.7 — $P^3_{s,t}$ is a t-threshold 3-uniform monotone CNF (corrected: s = 1 needs t ≥ 2)
-- statement:
--   Let $s$ be an integer and $t$ a natural number in the domain of the construction $P^3_{s,t}$: either $s\le0$; or $s=1$ and $t\ge2$; or $2\le s\le t$. Let $V=\{0,1,\dots,3t-s-1\}$, a set of $3t-s$ variables. Then $P^3_{s,t}$ is a valid CNF on $V$ (every clause uses only variables of $V$), every clause has exactly three literals, all literals are positive, and every satisfying assignment sets at least $t$ variables to one:
--
--   $$P^3_{s,t}\ \text{is a } t\text{-threshold 3-uniform monotone CNF on } 3t-s \text{ variables.}$$
--
--   This is the witness side of the lower bounds in Theorem 3.10: together with the count of Fact 3.8 it shows that $\Phi_0(s,t)\ge\theta_t(P^3_{s,t})$.
--
--   Differences from the source:
--   - correction: the s = 1 branch for every t ≥ 1 → s = 1 only for t ≥ 2; reason: at t = 1 the branch is (t − 2)·K3 + T5 = (−1)·K3 + T5, which is undefined, and would sit on 3t − s = 2 variables while T5 needs 5
--   - encoding: n = 3t − s variables → the variable set {0, …, 3t − s − 1} ⊂ ℕ, with 3t − s computed in ℤ; reason: relabeling variables changes no clause, assignment or weight; on the stated ranges 3t − s ≥ 0
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.9, Fact 3.7 and the definition of P^3_{s,t} (Section 3.3)

import Definitions.Def_MajorityDepthThree_Exact_Supplement_Constructions

set_option autoImplicit false

namespace MajorityDepthThree.Exact.Supplement

open MajorityDepthThree.Exact

/-- Fact 3.7 (p. 9): on the `3t - s` variables `range (3t - s)`, `P^3_{s,t}` is a valid
`t`-threshold 3-uniform monotone CNF, for every `(s,t)` in the domain of its definition:
`s ≤ 0`; `s = 1` with `t ≥ 2` (corrected: the printed `t ≥ 1` would use `-1` copies of
`K₃` at `t = 1`); `2 ≤ s ≤ t`. -/
theorem construction_threshold (s : ℤ) (t : ℕ)
    (hdom : s ≤ 0 ∨ (s = 1 ∧ 2 ≤ t) ∨ (2 ≤ s ∧ s ≤ t)) :
    let V : Finset ℕ := Finset.range (3 * (t : ℤ) - s).toNat
    ValidCNF V (P3 s t) ∧ Uniform 3 (P3 s t) ∧ Monotone (P3 s t) ∧
      Threshold V (P3 s t) t := by sorry

end MajorityDepthThree.Exact.Supplement
