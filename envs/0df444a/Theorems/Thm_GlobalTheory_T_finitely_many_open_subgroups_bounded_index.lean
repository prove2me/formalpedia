-- Prove2me | Theorems.Thm_GlobalTheory_T_finitely_many_open_subgroups_bounded_index
-- name    : GlobalTheory.T.finitely_many_open_subgroups_bounded_index
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:13.772826+00:00
-- url     : https://prove2.me/theorems/08486c60-c44e-5066-adb9-6ad3dd1c15a1
-- title:
--   T: finitely many open subgroups bounded index
-- statement:
--   The T construction uses the finitely many open subgroups bounded index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FinitelyManyOpenSubgroupsBoundedIndexStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FinitelyManyOpenSubgroupsBoundedIndexStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FinitelyManyOpenSubgroupsBoundedIndex
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FinitelyManyOpenSubgroupsBoundedIndexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finitely_many_open_subgroups_bounded_index : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ Module.finrank F E ≤ N}.Finite) → ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) | IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by sorry
