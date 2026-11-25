-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotientMk_surjective
-- name    : GroundTheory.Automorphic.Parabolic.quotientMk_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:38.280156+00:00
-- url     : https://prove2.me/theorems/ba4843b5-77c5-5d1d-b4cc-c5b6af62a7f9
-- title:
--   Parabolic: quotient Mk surjective
-- statement:
--   The Parabolic construction uses the quotient Mk surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L25-L27

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

theorem GroundTheory.Automorphic.Parabolic.quotientMk_surjective (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) :
    Function.Surjective (quotientMk Y hY) := by sorry
