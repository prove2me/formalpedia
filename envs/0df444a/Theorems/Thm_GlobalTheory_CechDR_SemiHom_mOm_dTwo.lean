-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dTwo
-- name    : GlobalTheory.CechDR.SemiHom.mOm_dTwo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:54.78665+00:00
-- url     : https://prove2.me/theorems/819923f4-8630-48c5-8fe6-411832ba20ae
-- title:
--   Semi Hom: m Om d Two
-- statement:
--   The Semi Hom construction uses the m Om d Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L465-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L465-L466

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

theorem GlobalTheory.CechDR.SemiHom.mOm_dTwo (h : SemiHom σ α) (x : Om R B 2) : h.mOm 3 (dTwo R B x) = dTwo R' B' (h.mOm 2 x) := by sorry
