-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_exists_rightCoaction
-- name    : GlobalTheory.CompanionTheory.FreeQuotProof.Chart.exists_rightCoaction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:58.910232+00:00
-- url     : https://prove2.me/theorems/bc127e1f-698b-44cf-a9c4-656febf42633
-- title:
--   Chart: exists right Coaction
-- statement:
--   The Chart construction uses the exists right Coaction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean#L93-L99

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
variable {R : Type} [CommRing R]
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
variable {H Z : Over (Spec (CommRingCat.of R))} [GrpObj H] [ModObj H Z]

theorem GlobalTheory.CompanionTheory.FreeQuotProof.Chart.exists_rightCoaction (i : specOver R Λ ⟶ H) (v : specOver R B ≅ Z) :
    ∃ ρ : B →ₐ[R] B ⊗[R] Λ, specHom ρ ≫ v.hom =
      (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
        (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom) := by sorry
