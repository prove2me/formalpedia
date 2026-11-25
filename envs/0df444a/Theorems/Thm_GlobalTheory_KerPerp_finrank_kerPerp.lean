-- Prove2me | Theorems.Thm_GlobalTheory_KerPerp_finrank_kerPerp
-- name    : GlobalTheory.KerPerp.finrank_kerPerp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:48.989298+00:00
-- url     : https://prove2.me/theorems/f1aa5031-c77d-5dc7-9018-133c278411e8
-- title:
--   Ker Perp: finrank ker Perp
-- statement:
--   The Ker Perp construction uses the finrank ker Perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L98-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.KerPerp
variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}
variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}
variable (hadj)

theorem GlobalTheory.KerPerp.finrank_kerPerp [Module.Free ℤ Y] [Module.Finite ℤ Y] (hb : Function.Bijective EF)
    (hy : Function.Surjective y) : Module.finrank ℤ (kerPerp hadj y) = Module.finrank ℤ Y := by sorry
