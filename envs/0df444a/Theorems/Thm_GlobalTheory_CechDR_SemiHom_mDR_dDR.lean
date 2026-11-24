-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_mDR_dDR
-- name    : GlobalTheory.CechDR.SemiHom.mDR_dDR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:00.689958+00:00
-- url     : https://prove2.me/theorems/15548dd3-c80f-41f3-930b-845e57a83655
-- title:
--   Semi Hom: m DR d DR
-- statement:
--   The Semi Hom construction uses the m DR d DR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L426-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L426-L431

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

theorem GlobalTheory.CechDR.SemiHom.mDR_dDR (h : SemiHom σ α) (x : DR R B) : h.mDR (dDR R B x) = dDR R' B' (h.mDR x) := by sorry
