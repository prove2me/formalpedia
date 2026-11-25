-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_quotient
-- name    : GroundTheory.Automorphic.Parabolic.isSmooth_quotient
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:34.217831+00:00
-- url     : https://prove2.me/theorems/dd93cc15-6706-5c35-80ed-5bf78bbb06a3
-- title:
--   Parabolic: is Smooth quotient
-- statement:
--   The Parabolic construction uses the is Smooth quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L29-L35

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

theorem GroundTheory.Automorphic.Parabolic.isSmooth_quotient [TopologicalSpace G] [IsTopologicalGroup G] (hτ : IsSmooth τ) (Y : Submodule ℂ U)
    (hY : ∀ g, Y ≤ Y.comap (τ g)) : IsSmooth (Representation.quotient τ Y hY) := by sorry
