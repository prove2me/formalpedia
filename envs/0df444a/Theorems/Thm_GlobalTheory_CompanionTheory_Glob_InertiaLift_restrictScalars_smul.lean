-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_restrictScalars_smul
-- name    : GlobalTheory.CompanionTheory.Glob.InertiaLift.restrictScalars_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:07.335212+00:00
-- url     : https://prove2.me/theorems/5fcc9304-fde8-5daf-bc7d-d3b729c3472b
-- title:
--   Inertia Lift: restrict Scalars smul
-- statement:
--   The Inertia Lift construction uses the restrict Scalars smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean#L18-L23

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
omit [NumberField F] [NumberField K]

theorem GlobalTheory.CompanionTheory.Glob.InertiaLift.restrictScalars_smul (h : Ω ≃ₐ[K] Ω) (A : ValuationSubring Ω) :
    (h.restrictScalars F) • A = h • A := by sorry
