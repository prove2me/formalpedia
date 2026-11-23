-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq
-- name    : GlobalTheory.ThetaTranslSpan.exists_im_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:02.152463+00:00
-- url     : https://prove2.me/theorems/5908449c-f58f-49f9-9389-99fb1a2fbde9
-- title:
--   Theta Transl Span: exists im eq
-- statement:
--   The Theta Transl Span construction uses the exists im eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsImEqLattice.lean#L83-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsImEqLattice.lean#L83-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem GlobalTheory.ThetaTranslSpan.exists_im_eq (hH : Hm.PosDef) (f : (Fin g → ℂ) →ₗ[ℝ] ℝ) :
    ∃ y, ∀ a, (star y ⬝ᵥ Hm.mulVec a).im = f a := by sorry
