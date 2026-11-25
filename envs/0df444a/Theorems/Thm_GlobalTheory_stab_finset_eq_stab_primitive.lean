-- Prove2me | Theorems.Thm_GlobalTheory_stab_finset_eq_stab_primitive
-- name    : GlobalTheory.stab_finset_eq_stab_primitive
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:29:23.013252+00:00
-- url     : https://prove2.me/theorems/4da91fc0-e74e-451d-9472-d1014ff3d555
-- title:
--   Global Theory: stab finset eq stab primitive
-- statement:
--   The Global Theory construction uses the stab finset eq stab primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimitiveElementStabilizerFinset.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimitiveElementStabilizerFinset.lean#L5-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimitiveElementStabilizerFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by sorry
