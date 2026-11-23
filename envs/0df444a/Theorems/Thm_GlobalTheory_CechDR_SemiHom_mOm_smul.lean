-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_smul
-- name    : GlobalTheory.CechDR.SemiHom.mOm_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:02.840538+00:00
-- url     : https://prove2.me/theorems/8650da26-6ad8-4b2f-b6df-a236efc10b03
-- title:
--   Semi Hom: m Om smul
-- statement:
--   The Semi Hom construction uses the m Om smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L456-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L456-L457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
variable {σ : R →+* R'} {α : B →+* B'}

theorem GlobalTheory.CechDR.SemiHom.mOm_smul (h : SemiHom σ α) {j : ℕ} (b : B) (x : Om R B j) :
    h.mOm j (b • x) = α b • h.mOm j x := by sorry
