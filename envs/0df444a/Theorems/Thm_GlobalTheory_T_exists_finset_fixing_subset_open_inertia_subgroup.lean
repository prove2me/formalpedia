-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_fixing_subset_open_inertia_subgroup
-- name    : GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:55.510093+00:00
-- url     : https://prove2.me/theorems/e5e3b7a5-e55c-4ef5-9afd-d412cfcd93b8
-- title:
--   T: exists finset fixing subset open inertia subgroup
-- statement:
--   The T construction uses the exists finset fixing subset open inertia subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingSubsetOpenInertiaSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by sorry
