-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_stabilizer_le_intUnits
-- name    : GlobalTheory.UnitLemma.stabilizer_le_intUnits
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:58.939016+00:00
-- url     : https://prove2.me/theorems/defc7c67-2208-4191-832e-81eabb1f59ee
-- title:
--   Unit Lemma: stabilizer le int Units
-- statement:
--   The Unit Lemma construction uses the stabilizer le int Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticeLeIntegralUnitsSubgroup.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticeLeIntegralUnitsSubgroup.lean#L48-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem GlobalTheory.UnitLemma.stabilizer_le_intUnits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by sorry
