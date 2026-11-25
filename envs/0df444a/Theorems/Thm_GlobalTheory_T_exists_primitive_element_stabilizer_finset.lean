-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_primitive_element_stabilizer_finset
-- name    : GlobalTheory.T.exists_primitive_element_stabilizer_finset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:36.988128+00:00
-- url     : https://prove2.me/theorems/f6c89ef7-e126-44cf-b44d-695f7e3fcaa9
-- title:
--   T: exists primitive element stabilizer finset
-- statement:
--   The T construction uses the exists primitive element stabilizer finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimitiveElementStabilizerFinsetStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimitiveElementStabilizerFinsetStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimitiveElementStabilizerFinset
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimitiveElementStabilizerFinsetStatement
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

theorem GlobalTheory.T.exists_primitive_element_stabilizer_finset : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by sorry
