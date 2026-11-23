-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- name    : GlobalTheory.CechDR.SemiHom.coe_mOm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:07.618642+00:00
-- url     : https://prove2.me/theorems/4cb0bf52-0863-4d05-b20c-9f1d384650ec
-- title:
--   Semi Hom: coe m Om
-- statement:
--   The Semi Hom construction uses the coe m Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L454-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L454-L454

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

theorem GlobalTheory.CechDR.SemiHom.coe_mOm (h : SemiHom σ α) {j : ℕ} (x : Om R B j) : (h.mOm j x : DR R' B') = h.mDR x := by sorry

attribute [defeq] GlobalTheory.CechDR.SemiHom.coe_mOm
