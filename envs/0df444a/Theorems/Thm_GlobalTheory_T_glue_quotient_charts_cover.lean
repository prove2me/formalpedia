-- Prove2me | Theorems.Thm_GlobalTheory_T_glue_quotient_charts_cover
-- name    : GlobalTheory.T.glue_quotient_charts_cover
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:23.224441+00:00
-- url     : https://prove2.me/theorems/5f2c5eed-c2ae-4868-8cb8-20132f646911
-- title:
--   T: glue quotient charts cover
-- statement:
--   The T construction uses the glue quotient charts cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/GlueQuotientChartsCoverStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/GlueQuotientChartsCoverStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCover
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCoverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.glue_quotient_charts_cover : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by sorry
