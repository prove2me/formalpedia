-- Prove2me | Theorems.Thm_GlobalTheory_AnValSecondLaw_jetRd_pe_two
-- name    : GlobalTheory.AnValSecondLaw.jetRd_pe_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:33.69999+00:00
-- url     : https://prove2.me/theorems/1e9fd92e-8729-4edf-9c16-75bb10d61fc8
-- title:
--   An Val Second Law: jet Rd pe two
-- statement:
--   The An Val Second Law construction uses the jet Rd pe two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSecondPartialLawTrivial.lean#L180-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSecondPartialLawTrivial.lean#L180-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSecondPartialLawTrivial
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
open GlobalTheory GlobalTheory.AnValSecondLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem GlobalTheory.AnValSecondLaw.jetRd_pe_two (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n' : ℕ}
    (φ φ' : Fin g → MvPolynomial (Fin n' × Fin g) ℂ)
    (B B' : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ j, (Ideal.Quotient.mk _ (φ j - MvPolynomial.C (MvPolynomial.constantCoeff (φ j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B w j))
    (h' : ∀ j, (Ideal.Quotient.mk _ (φ' j - MvPolynomial.C (MvPolynomial.constantCoeff (φ' j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B' w j)) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m ![φ, φ']) (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![B, B']) := by sorry
