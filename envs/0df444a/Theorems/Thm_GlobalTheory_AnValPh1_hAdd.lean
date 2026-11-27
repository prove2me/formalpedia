-- Prove2me | Theorems.Thm_GlobalTheory_AnValPh1_hAdd
-- name    : GlobalTheory.AnValPh1.hAdd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:34:52.094252+00:00
-- url     : https://prove2.me/theorems/ecc229a8-6873-4754-9a60-caa095e2ee8f
-- title:
--   An Val Ph1: h Add
-- statement:
--   The An Val Ph1 construction uses the h Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameFirstPartialLawTrivial.lean#L215-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameFirstPartialLawTrivial.lean#L215-L235

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

theorem GlobalTheory.AnValPh1.hAdd {n g : ℕ} (m : ℕ) (a b : Fin n) (hab : a ≠ b) (j : Fin g) :
    Ideal.Quotient.mk (orig ℂ (Fin n × Fin g) ^ (m + 1))
      (psIn g m ![a, b] (addF ℂ g j) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![a, b] (addF ℂ g j)))) =
      Ideal.Quotient.mk _ (∑ i ∈ ({a, b} : Finset (Fin n)), MvPolynomial.X (i, j)) := by sorry
