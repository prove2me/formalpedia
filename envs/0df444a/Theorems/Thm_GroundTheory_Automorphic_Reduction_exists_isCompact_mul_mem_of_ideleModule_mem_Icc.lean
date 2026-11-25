-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_isCompact_mul_mem_of_ideleModule_mem_Icc
-- name    : GroundTheory.Automorphic.Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:29.579517+00:00
-- url     : https://prove2.me/theorems/705a68b7-2327-4ab9-a807-59577c50a856
-- title:
--   Reduction: exists is Compact mul mem of idele Module mem Icc
-- statement:
--   The Reduction construction uses the exists is Compact mul mem of idele Module mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIdele.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIdele.lean#L14-L37

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ S : Set (IdeleGroup K), IsCompact S ∧ ∀ s : IdeleGroup K,
      a ≤ (ideleModule K s : ℝ) → (ideleModule K s : ℝ) ≤ b → ∃ c : Kˣ, diagonal K c * s ∈ S := by sorry
