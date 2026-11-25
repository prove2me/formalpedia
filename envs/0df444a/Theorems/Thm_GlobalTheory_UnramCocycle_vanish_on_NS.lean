-- Prove2me | Theorems.Thm_GlobalTheory_UnramCocycle_vanish_on_NS
-- name    : GlobalTheory.UnramCocycle.vanish_on_NS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:03.650802+00:00
-- url     : https://prove2.me/theorems/f350e5d5-f31f-4adc-8b48-aa5c5fafbf34
-- title:
--   Unram Cocycle: vanish on NS
-- statement:
--   The Unram Cocycle construction uses the vanish on NS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean#L87-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean#L87-L121

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise
open GlobalTheory GlobalTheory.UnramCocycle

theorem GlobalTheory.UnramCocycle.vanish_on_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by sorry
