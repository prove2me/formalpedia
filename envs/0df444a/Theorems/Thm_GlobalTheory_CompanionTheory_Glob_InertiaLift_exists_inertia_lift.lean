-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_exists_inertia_lift
-- name    : GlobalTheory.CompanionTheory.Glob.InertiaLift.exists_inertia_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:57.768822+00:00
-- url     : https://prove2.me/theorems/6a40f672-f3f0-579c-aa52-43deffaf73df
-- title:
--   Inertia Lift: exists inertia lift
-- statement:
--   The Inertia Lift construction uses the exists inertia lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L112-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L112-L186

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

theorem GlobalTheory.CompanionTheory.Glob.InertiaLift.exists_inertia_lift [IsAlgClosure F Ω] [IsAlgClosure K Ω] [Normal F K]
    (w : HeightOneSpectrum (𝓞 K)) {τ : K ≃ₐ[F] K} (hτ : τ ∈ w.asIdeal.inertia (K ≃ₐ[F] K)) :
    ∃ (A : ValuationSubring Ω) (σ : Ω ≃ₐ[F] Ω),
      (∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal) ∧
      σ ∈ Inertia (F := F) A ∧ ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by sorry
