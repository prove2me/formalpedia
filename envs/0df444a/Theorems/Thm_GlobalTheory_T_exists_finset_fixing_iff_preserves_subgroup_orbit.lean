-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_fixing_iff_preserves_subgroup_orbit
-- name    : GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:40:34.313085+00:00
-- url     : https://prove2.me/theorems/4f6ceccf-2494-5fc5-851b-f1408123dc7e
-- title:
--   T: exists finset fixing iff preserves subgroup orbit
-- statement:
--   The T construction uses the exists finset fixing iff preserves subgroup orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetFixingIffPreservesSubgroupOrbitStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetFixingIffPreservesSubgroupOrbitStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingIffPreservesSubgroupOrbit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingIffPreservesSubgroupOrbitStatement
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

theorem GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω), ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by sorry
