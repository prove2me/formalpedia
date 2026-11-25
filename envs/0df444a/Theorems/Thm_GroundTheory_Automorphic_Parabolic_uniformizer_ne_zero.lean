-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero
-- name    : GroundTheory.Automorphic.Parabolic.uniformizer_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:04.259877+00:00
-- url     : https://prove2.me/theorems/3c4b976c-370f-4598-8c39-9790a9d7f845
-- title:
--   Parabolic: uniformizer ne zero
-- statement:
--   The Parabolic construction uses the uniformizer ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L15-L16

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
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

theorem GroundTheory.Automorphic.Parabolic.uniformizer_ne_zero : (GLnLocal.uniformizer F : F) ≠ 0 := by sorry
