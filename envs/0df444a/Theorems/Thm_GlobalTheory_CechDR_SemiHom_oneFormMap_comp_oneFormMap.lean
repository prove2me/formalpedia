-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap
-- name    : GlobalTheory.CechDR.SemiHom.oneFormMap_comp_oneFormMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:22.171366+00:00
-- url     : https://prove2.me/theorems/f0ec36be-7d10-4101-92b6-787d6b4376cc
-- title:
--   Semi Hom: one Form Map comp one Form Map
-- statement:
--   The Semi Hom construction uses the one Form Map comp one Form Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L493-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L493-L498

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
variable {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}

theorem GlobalTheory.CechDR.SemiHom.oneFormMap_comp_oneFormMap (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ) (e : ∀ b, β (α b) = γ b)
    (ω : Ω[B⁄R]) : h'.m1 (h.m1 ω) = h''.m1 ω := by sorry
