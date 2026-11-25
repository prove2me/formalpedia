-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_comp_fromOfGlobalSections
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.comp_fromOfGlobalSections
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:30.079232+00:00
-- url     : https://prove2.me/theorems/8c5f77da-e044-5c08-b874-86f57f2a848c
-- title:
--   Proj Hom: comp from Of Global Sections
-- statement:
--   The Proj Hom construction uses the comp from Of Global Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L168-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L168-L188

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

theorem GroundTheory.Arith.SchemeCoh.ProjHom.comp_fromOfGlobalSections {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) {Y : Scheme.{u}}
    (h : Y ⟶ X) :
    h ≫ Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 (h.appTop.hom.comp f)
      (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by sorry
