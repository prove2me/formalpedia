-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_hasAffineChart_of_open
-- name    : GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_open
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:44.952345+00:00
-- url     : https://prove2.me/theorems/e511d16f-5564-442f-af0d-9a5a10e939c7
-- title:
--   Chart: has Affine Chart of open
-- statement:
--   The Chart construction uses the has Affine Chart of open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean#L356-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean#L356-L394

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory.AffineQuotient
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Chart
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]

theorem GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_open (V : X.left.Opens)
    (hst : (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V)
    [ModObj G (Over.mk (V.ι ≫ X.hom))]
    (hm : (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)) ≫
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) =
      G ◁ (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ γ[G, X])
    (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (hY : IsAffine Y) (h₁ : IsFinite q) (h₂ : Flat q)
    (h₃ : LocallyOfFinitePresentation q) (h₄ : Surjective q)
    (pb : IsPullback (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)).left
      (snd G (Over.mk (V.ι ≫ X.hom))).left q q) :
    HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by sorry
