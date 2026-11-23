-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_explicit_source_witness
-- name    : HodgeComputer.CycleQ2.normalChart_explicit_source_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T21:19:27.846899+00:00
-- url     : https://prove2.me/theorems/d92115d2-1e48-404b-91e3-4bdea762dc05
-- title:
--   Cycle-q2 normal chart with an explicit source factor
-- statement:
--   Let $F$ be the cyclic sextic and $A$ the monomial source of the cycle-$q2$ instance, and set $B = A/2$.
--
--   The normal-chart residue is linear in the numerator components $W$ once a denominator $S$ is fixed. Its undifferentiated source factor is
--
--   $$\Delta_0 = \partial_0 F \cdot \partial_0 B - B \cdot \partial_0 \partial_0 F.$$
--
--   Expanding the two derivatives writes $\Delta_0$ as the explicit polynomial `explicitSource`. Replacing $\Delta_0$ by that polynomial produces `explicitResidue(S, W)`.
--
--   The claim is that there exist a nonzero homogeneous $S$ of degree at least $2$, coprime to $F$, and homogeneous numerator components $W_j$ of degree $\deg S + 7$, together with a polynomial $Q$, such that
--
--   $$\mathrm{explicitResidue}(S, W) = F^2 Q.$$
--
--   This is the degree-at-least-two witness with the source factor written out. It is equivalent to the original residue equation, because $\Delta_0$ and `explicitSource` are the same polynomial.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_degree_at_least_two_witness, https://prove2.me/theorems/9d6b8844-bf65-41ca-91c2-d58c37bc0f39. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2ExplicitSource

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

/-- The degree-at-least-two normal-chart equation with the source factor expanded. -/
theorem HodgeComputer.CycleQ2.normalChart_explicit_source_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      explicitResidue S W = F ^ 2 * Q := by
  sorry
