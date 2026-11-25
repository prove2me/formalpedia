-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_mem_inertia_of_integers
-- name    : GlobalTheory.CompanionTheory.Glob.InertiaLift.mem_inertia_of_integers
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:39.525047+00:00
-- url     : https://prove2.me/theorems/501281c5-771d-5f92-8def-40d056717421
-- title:
--   Inertia Lift: mem inertia of integers
-- statement:
--   The Inertia Lift construction uses the mem inertia of integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L27-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open scoped Pointwise IntermediateField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob GlobalTheory.CompanionTheory.Glob.InertiaLift
variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
omit [NumberField K] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

theorem GlobalTheory.CompanionTheory.Glob.InertiaLift.mem_inertia_of_integers [IsAlgClosure F Ω] {A : ValuationSubring Ω} {σ : Ω ≃ₐ[F] Ω}
    (hd : σ • A = A) (hb : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) :
    σ ∈ Inertia (F := F) A := by sorry
