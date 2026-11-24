-- Prove2me | Theorems.Thm_GlobalTheory_MuTowerInj_ker_le_range
-- name    : GlobalTheory.MuTowerInj.ker_le_range
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:44.75163+00:00
-- url     : https://prove2.me/theorems/19d0a912-496f-4c16-9cce-fca412c5d718
-- title:
--   Mu Tower Inj: ker le range
-- statement:
--   The Mu Tower Inj construction uses the ker le range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L44-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L44-L90

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]

theorem GlobalTheory.MuTowerInj.ker_le_range [ContinuousMul Γ] (ρ₁ : Representation R₁ Γ M₁)
    (ρ₂ : Representation R₂ Γ M₂) (ρ₃ : Representation R₃ Γ M₃) (h₂ : ContAction ρ₂)
    (u : M₁ →+ M₂) (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m))
    (p : M₂ →+ M₃) (hp : ∀ g m, p (ρ₂ g m) = ρ₃ g (p m))
    (hinj : Function.Injective u) (hsurj : Function.Surjective p)
    (hex : ∀ m, p m = 0 → ∃ k, u k = m) :
    (secondCohomologyMapOfEquivariantAdd ρ₂ ρ₃ p hp).ker ≤ (secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu).range := by sorry
