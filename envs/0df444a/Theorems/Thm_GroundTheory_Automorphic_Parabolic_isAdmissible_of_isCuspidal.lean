-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isAdmissible_of_isCuspidal
-- name    : GroundTheory.Automorphic.Parabolic.isAdmissible_of_isCuspidal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:08.672642+00:00
-- url     : https://prove2.me/theorems/212c733d-ed35-50ba-a751-8b097291b44f
-- title:
--   Parabolic: is Admissible of is Cuspidal
-- statement:
--   The Parabolic construction uses the is Admissible of is Cuspidal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L271-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L271-L481

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.isAdmissible_of_isCuspidal {σ : Representation ℂ (levi F n β) W} [σ.IsIrreducible]
    (hσ : IsSmooth σ) (hc : IsCuspidal σ) : IsAdmissible σ := by sorry
