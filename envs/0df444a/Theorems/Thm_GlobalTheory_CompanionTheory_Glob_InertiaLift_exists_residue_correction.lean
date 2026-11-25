-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_exists_residue_correction
-- name    : GlobalTheory.CompanionTheory.Glob.InertiaLift.exists_residue_correction
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:01:27.654656+00:00
-- url     : https://prove2.me/theorems/4d03a5f3-7eac-4667-8e00-87cf1b5e64e3
-- title:
--   Inertia Lift: exists residue correction
-- statement:
--   The Inertia Lift construction uses the exists residue correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L67-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L67-L110

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

theorem GlobalTheory.CompanionTheory.Glob.InertiaLift.exists_residue_correction [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    (w : HeightOneSpectrum (𝓞 K))
    (hA : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal)
    {σ₁ : Ω ≃ₐ[F] Ω} (hd : σ₁ ∈ Dec (F := F) A)
    (hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1) :
    ∃ h : Ω ≃ₐ[K] Ω, h • A = A ∧ ∀ b : IntCl K Ω, A.valuation (h (b : Ω) - σ₁ b) < 1 := by sorry
