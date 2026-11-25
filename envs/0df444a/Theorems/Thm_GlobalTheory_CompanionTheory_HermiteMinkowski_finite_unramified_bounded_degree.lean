-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermiteMinkowski_finite_unramified_bounded_degree
-- name    : GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:00:06.639627+00:00
-- url     : https://prove2.me/theorems/4277aefa-4893-53b9-ba80-e97407ddbe44
-- title:
--   Hermite Minkowski: finite unramified bounded degree
-- statement:
--   The Hermite Minkowski construction uses the finite unramified bounded degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HermiteFinitelyManyUnramifiedExtensions.lean#L41-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HermiteFinitelyManyUnramifiedExtensions.lean#L41-L74

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePowerStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminantStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory.CompanionTheory.HermiteMinkowski

theorem GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ),
      {E : IntermediateField F Ω | FiniteDimensional F E ∧
        IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧
        Module.finrank F E ≤ N}.Finite := by sorry
