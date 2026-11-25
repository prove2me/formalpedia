-- Prove2me | Theorems.Thm_GlobalTheory_T_hermite_finitely_many_unramified_extensions
-- name    : GlobalTheory.T.hermite_finitely_many_unramified_extensions
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:43.236728+00:00
-- url     : https://prove2.me/theorems/b9b09157-2fe9-4821-ab4b-1b6ed6721c0f
-- title:
--   T: hermite finitely many unramified extensions
-- statement:
--   The T construction uses the hermite finitely many unramified extensions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HermiteFinitelyManyUnramifiedExtensionsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HermiteFinitelyManyUnramifiedExtensionsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensionsStatement
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

theorem GlobalTheory.T.hermite_finitely_many_unramified_extensions : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ), {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧ Module.finrank F E ≤ N}.Finite := by sorry
