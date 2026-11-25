-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_isCompact_add_mem
-- name    : GroundTheory.Automorphic.Reduction.exists_isCompact_add_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:28.299076+00:00
-- url     : https://prove2.me/theorems/7cf6b5c2-802b-40b8-9af6-6da307fc27ff
-- title:
--   Reduction: exists is Compact add mem
-- statement:
--   The Reduction construction uses the exists is Compact add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L60-L66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.exists_isCompact_add_mem :
    ∃ D : Set 𝔸[K], IsCompact D ∧ ∀ x : 𝔸[K], ∃ k : K, x + algebraMap K 𝔸[K] k ∈ D := by sorry
