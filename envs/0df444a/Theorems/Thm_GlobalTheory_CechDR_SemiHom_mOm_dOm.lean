-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dOm
-- name    : GlobalTheory.CechDR.SemiHom.mOm_dOm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:17.568437+00:00
-- url     : https://prove2.me/theorems/8f06aca0-4082-4df3-9ab8-cf008a05f0a8
-- title:
--   Semi Hom: m Om d Om
-- statement:
--   The Semi Hom construction uses the m Om d Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L459-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L459-L460

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

theorem GlobalTheory.CechDR.SemiHom.mOm_dOm (h : SemiHom σ α) {j : ℕ} (x : Om R B j) :
    h.mOm (j + 1) (dOm R B j x) = dOm R' B' j (h.mOm j x) := by sorry
