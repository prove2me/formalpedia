-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_corr_fromOfGlobalSections
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.corr_fromOfGlobalSections
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:03.292832+00:00
-- url     : https://prove2.me/theorems/9d5feaa7-5117-49b0-b8eb-7040e8cc9247
-- title:
--   Proj Hom: corr from Of Global Sections
-- statement:
--   The Proj Hom construction uses the corr from Of Global Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L57-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L57-L75

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

theorem GroundTheory.Arith.SchemeCoh.ProjHom.corr_fromOfGlobalSections {r : A} {d : ℕ} (hd : 0 < d) (hr : r ∈ 𝒜 d) (k : ℕ) (a : A)
    (ha : a ∈ 𝒜 (k • d)) :
    corr 𝒜 (Proj.fromOfGlobalSections 𝒜 f hf) r (X.basicOpen (f r))
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd hr).ge (Away.mk 𝒜 hr k a ha) *
      (X.basicOpen (f r)).ι.appTop (f r) ^ k = (X.basicOpen (f r)).ι.appTop (f a) := by sorry
