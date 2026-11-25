-- Prove2me | Theorems.Thm_GlobalTheory_KerPerp_isotropic
-- name    : GlobalTheory.KerPerp.isotropic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:28.679712+00:00
-- url     : https://prove2.me/theorems/aa62486b-6534-4498-8fea-5db212b3da8e
-- title:
--   Ker Perp: isotropic
-- statement:
--   The Ker Perp construction uses the isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L34-L35

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

theorem GlobalTheory.KerPerp.isotropic (hle : kerPerp hadj y ≤ LinearMap.ker y) {t t' : L} (ht : t ∈ kerPerp hadj y)
    (ht' : t' ∈ kerPerp hadj y) : EF t t' = 0 := by sorry
