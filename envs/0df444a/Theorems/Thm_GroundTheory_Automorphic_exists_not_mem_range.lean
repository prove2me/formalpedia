-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_not_mem_range
-- name    : GroundTheory.Automorphic.exists_not_mem_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:35.382928+00:00
-- url     : https://prove2.me/theorems/80060a11-0930-4b12-98b9-6203417270a7
-- title:
--   Automorphic: exists not mem range
-- statement:
--   The Automorphic construction uses the exists not mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L28-L35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
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
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem GroundTheory.Automorphic.exists_not_mem_range : ∃ ζ : E, ζ ∉ Set.range (algebraMap F E) := by sorry
