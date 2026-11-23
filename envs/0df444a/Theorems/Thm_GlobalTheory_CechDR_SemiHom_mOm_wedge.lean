-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_wedge
-- name    : GlobalTheory.CechDR.SemiHom.mOm_wedge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:38.594932+00:00
-- url     : https://prove2.me/theorems/fd459dc1-6125-4f99-be55-ddbbee7545ed
-- title:
--   Semi Hom: m Om wedge
-- statement:
--   The Semi Hom construction uses the m Om wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L468-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L468-L469

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

theorem GlobalTheory.CechDR.SemiHom.mOm_wedge (h : SemiHom σ α) (a b : Ω[B⁄R]) :
    h.mOm 2 (wedge R B a b) = wedge R' B' (h.m1 a) (h.m1 b) := by sorry
