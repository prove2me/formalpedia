-- Prove2me | Theorems.Thm_GlobalTheory_AnValPh1_lift_jet
-- name    : GlobalTheory.AnValPh1.lift_jet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:39:13.099877+00:00
-- url     : https://prove2.me/theorems/c379c5ec-2288-4789-b1c7-b82646823f4c
-- title:
--   An Val Ph1: lift jet
-- statement:
--   The An Val Ph1 construction uses the lift jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameFirstPartialLawTrivial.lean#L127-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameFirstPartialLawTrivial.lean#L127-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameFirstPartialLawTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnValPh1.lift_jet {S : Scheme.{0}} {P Q : Over S} {N m : ℕ} {R : Type} [CommRing R]
    (r : Jet ℂ (Fin 1 × Fin N) m →+* R) (u : Sp R ⟶ S) (x : Sp ℂ ⟶ S)
    (a : Over.mk u ⟶ P) (b : Over.mk u ⟶ Q) (f : (Fin N → ℂ) → (Over.mk x ⟶ P)) (h : (Fin N → ℂ) → (Over.mk x ⟶ Q))
    (hf : IsHolFam fun v => (f v).left) (hh : IsHolFam fun v => (h v).left)
    (ea : a.left = spMap r ≫ jetPt _ hf m) (eb : b.left = spMap r ≫ jetPt _ hh m) :
    ∃ hq : IsHolFam (fun v => (lift (f v) (h v)).left), (lift a b).left = spMap r ≫ jetPt _ hq m := by sorry
