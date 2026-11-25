-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotientMk_apply
-- name    : GroundTheory.Automorphic.Parabolic.quotientMk_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:09.561798+00:00
-- url     : https://prove2.me/theorems/8797ee3a-2142-5e3f-9e42-c4504e74f268
-- title:
--   Parabolic: quotient Mk apply
-- statement:
--   The Parabolic construction uses the quotient Mk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L22-L23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}

theorem GroundTheory.Automorphic.Parabolic.quotientMk_apply (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) (x : U) :
    quotientMk Y hY x = Submodule.Quotient.mk x := by sorry
