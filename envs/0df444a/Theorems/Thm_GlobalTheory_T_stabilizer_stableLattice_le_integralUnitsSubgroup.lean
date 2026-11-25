-- Prove2me | Theorems.Thm_GlobalTheory_T_stabilizer_stableLattice_le_integralUnitsSubgroup
-- name    : GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:21.75026+00:00
-- url     : https://prove2.me/theorems/4895ff9b-9a47-56fc-836a-4a8b757dafb3
-- title:
--   T: stabilizer stable Lattice le integral Units Subgroup
-- statement:
--   The T construction uses the stabilizer stable Lattice le integral Units Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticeLeIntegralUnitsSubgroupStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticeLeIntegralUnitsSubgroupStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by sorry
