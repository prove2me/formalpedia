-- Prove2me | Theorems.Thm_GlobalTheory_CMFormBound_val_mul
-- name    : GlobalTheory.CMFormBound.val_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:03:06.693591+00:00
-- url     : https://prove2.me/theorems/a8015b95-2abd-46a2-8359-e493818218c6
-- title:
--   CMForm Bound: val mul
-- statement:
--   The CMForm Bound construction uses the val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L48-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem GlobalTheory.CMFormBound.val_mul (l : ℕ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    val_vp O l (x * y) = val_vp O l x + val_vp O l y := by sorry
