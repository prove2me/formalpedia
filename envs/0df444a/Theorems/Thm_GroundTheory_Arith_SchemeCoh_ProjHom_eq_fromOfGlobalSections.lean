-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_eq_fromOfGlobalSections
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.eq_fromOfGlobalSections
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:56.026791+00:00
-- url     : https://prove2.me/theorems/d62aa1c5-1dee-4e59-886f-6de85c4a71bd
-- title:
--   Proj Hom: eq from Of Global Sections
-- statement:
--   The Proj Hom construction uses the eq from Of Global Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L151-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L151-L164

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjHom
variable {X : Scheme.{u}}
variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
variable {𝒜}

theorem GroundTheory.Arith.SchemeCoh.ProjHom.eq_fromOfGlobalSections {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) (g : X ⟶ Proj 𝒜)
    (hg : ∀ i, g ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = X.basicOpen (f (r i)))
    (hc : ∀ i k a (ha : a ∈ 𝒜 (k • d i)),
      corr 𝒜 g (r i) _ (hg i).ge (Away.mk 𝒜 (hr i) k a ha) *
        (X.basicOpen (f (r i))).ι.appTop (f (r i)) ^ k =
        (X.basicOpen (f (r i))).ι.appTop (f a)) :
    g = Proj.fromOfGlobalSections 𝒜 f hf := by sorry
