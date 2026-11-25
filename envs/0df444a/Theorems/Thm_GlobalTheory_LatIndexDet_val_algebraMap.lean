-- Prove2me | Theorems.Thm_GlobalTheory_LatIndexDet_val_algebraMap
-- name    : GlobalTheory.LatIndexDet.val_algebraMap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:35.051535+00:00
-- url     : https://prove2.me/theorems/33351c3c-f77a-4ba0-bbc0-44a1d863cc07
-- title:
--   Lat Index Det: val algebra Map
-- statement:
--   The Lat Index Det construction uses the val algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapDetRestrict.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapDetRestrict.lean#L11-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapDetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LatIndexDet

theorem GlobalTheory.LatIndexDet.val_algebraMap (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] {d : O} (hd : d ≠ 0) :
    val O (algebraMap O E d) = ((IsDiscreteValuationRing.addVal O d).toNat : ℤ) := by sorry
