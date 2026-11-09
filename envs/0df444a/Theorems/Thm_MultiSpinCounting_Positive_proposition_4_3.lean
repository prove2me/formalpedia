-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_proposition_4_3
-- name    : MultiSpinCounting.Positive.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:34.444132+00:00
-- url     : https://prove2.me/theorems/021ba0b8-de2f-428b-b374-e0f550a93700
-- title:
--   Proposition 4.3 — one-step Hilbert-diameter recursion
-- statement:
--   For a positive rational query $(\Phi,v,t)$ with fixed $P\ge3$, the Hilbert diameter is a finite attained maximum. It is zero if $v$ is isolated. Otherwise
--   $$\operatorname{diam}_H\mathcal P_0(\Phi,v)\le\sum_i\Delta_B(A_{v,v_i}),$$
--   and for $t=s+1$,
--   $$\operatorname{diam}_H\mathcal P_{s+1}(\Phi,v)\le\max_{a\ne b}\sum_i\left(c_B(A_{v,v_i})\operatorname{diam}_H\mathcal P_s(\Phi^v_{i,a,b},v_i)+2\xi_P\right).$$
--   The child diameters are also asserted to be well-defined. In particular, the rounding term occurs once for each neighbor.
--
--   This is the source’s local accuracy estimate, with positivity and boundedness ensuring that the displayed diameters have their intended meaning.
--
--   Differences from the source:
--   - reading: admissible feasible query in §4 → every positive rational query with P ≥ 3; reason: §4 supplies no narrower definition; Fact 4.2 establishes feasibility for all these queries
--   - encoding: finite ordered vertex and spin sets → Fin n and Fin q, with an active vertex subset; reason: relabeling preserves every instance; active subsets implement the source sub-instances and the fixed vertex order
--   - encoding: Hilbert diameter is a maximum → sSup together with explicit positivity, boundedness and attainment conclusions; reason: the supremum therefore equals the source maximum, including for every child diameter
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 15, Proposition 4.3

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Polytopes

namespace MultiSpinCounting.Positive

/-- Proposition 4.3, p. 15. The rounding term is inside the neighbor sum. -/
theorem proposition_4_3 {n q : ℕ} (hq : 3 ≤ q) (Φ : Instance n q ℚ)
    (hΦ : IsPositive Φ) (P t : ℕ) (hP : 3 ≤ P) (v : Fin n) (hv : v ∈ Φ.active) :
    PolyWellDefined (polytope P t Φ v) ∧
    (if (neighbors Φ v).Nonempty then
      match t with
      | 0 => hilbertDiameter (polytope P 0 Φ v) ≤
          ∑ i ∈ neighbors Φ v, deltaB ((realInstance Φ).interaction v i)
      | s+1 =>
          (∀ a b : Fin q, a ≠ b → ∀ i ∈ neighbors Φ v,
            PolyWellDefined (polytope P s (child Φ v i a b) i)) ∧
          hilbertDiameter (polytope P (s+1) Φ v) ≤
            sSup {r : ℝ | ∃ a b : Fin q, a ≠ b ∧ r =
              ∑ i ∈ neighbors Φ v,
                (cB ((realInstance Φ).interaction v i) *
                  hilbertDiameter (polytope P s (child Φ v i a b) i) + 2*roundingAccuracy P)}
    else hilbertDiameter (polytope P t Φ v) = 0) := by sorry

end MultiSpinCounting.Positive
