-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_baseChange_compare
-- name    : GlobalTheory.CompanionTheory.FreeQuotProof.Chart.baseChange_compare
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:41:49.952812+00:00
-- url     : https://prove2.me/theorems/81fadc04-515a-4080-a17c-203e3058285f
-- title:
--   Chart: base Change compare
-- statement:
--   The Chart construction uses the base Change compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean#L437-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean#L437-L463

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
variable {S S' : Scheme.{0}} (j : S' ⟶ S)

theorem GlobalTheory.CompanionTheory.FreeQuotProof.Chart.baseChange_compare [Mono j] (G Z : Over S) [GrpObj G] [ModObj G Z] (z : Z.left ⟶ S')
    (hz : z ≫ j = Z.hom) :
    letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
    letI := modObjObj (Over.pullback j) G Z
    IsIso (pullback.fst Z.hom j) ∧
      ∃ e : (((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z)).left ≅ (G ⊗ Z).left,
      e.hom ≫ (γ[G, Z] : G ⊗ Z ⟶ Z).left =
        (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z).left ≫
          pullback.fst Z.hom j ∧
      e.hom ≫ (snd G Z).left =
        (snd ((Over.pullback j).obj G) ((Over.pullback j).obj Z)).left ≫ pullback.fst Z.hom j := by sorry
