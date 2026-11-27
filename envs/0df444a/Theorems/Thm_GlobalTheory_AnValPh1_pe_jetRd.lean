-- Prove2me | Theorems.Thm_GlobalTheory_AnValPh1_pe_jetRd
-- name    : GlobalTheory.AnValPh1.pe_jetRd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-27T05:39:02.151558+00:00
-- url     : https://prove2.me/theorems/1632cf46-6c11-43d6-8a7c-0a79cdb9349c
-- title:
--   An Val Ph1: pe jet Rd
-- statement:
--   The An Val Ph1 construction uses the pe jet Rd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameFirstPartialLawTrivial.lean#L150-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameFirstPartialLawTrivial.lean#L150-L174

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem GlobalTheory.AnValPh1.pe_jetRd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n : ℕ} (T : Fin 2 → Finset (Fin n))
    (hT : Disjoint (T 0) (T 1)) (φ : Fin 2 → Fin g → MvPolynomial (Fin n × Fin g) ℂ)
    (hφ : ∀ k j, Ideal.Quotient.mk (orig ℂ (Fin n × Fin g) ^ (m + 1))
      (φ k j - MvPolynomial.C (MvPolynomial.constantCoeff (φ k j))) =
      Ideal.Quotient.mk _ (∑ i ∈ T k, MvPolynomial.X (i, j))) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m φ) (fun K => psumL n g ⟨K.down.biUnion T⟩) := by sorry
