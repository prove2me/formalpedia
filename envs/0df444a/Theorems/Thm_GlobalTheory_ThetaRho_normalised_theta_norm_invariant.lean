-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRho_normalised_theta_norm_invariant
-- name    : GlobalTheory.ThetaRho.normalised_theta_norm_invariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:30:27.519923+00:00
-- url     : https://prove2.me/theorems/e670991d-6059-51d3-8bce-c9d476f5a2a4
-- title:
--   Theta Rho: normalised theta norm invariant
-- statement:
--   The Theta Rho construction uses the normalised theta norm invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaNormInvariant.lean#L305-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaNormInvariant.lean#L305-L332

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaNormInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRho
open MeasureTheory
open scoped ComplexConjugate

theorem GlobalTheory.ThetaRho.normalised_theta_norm_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ (A : TorusAt X.toData x) (A' : TorusAt X.toData (lact γ (rmul x b))) (v : Fin r → E), A'.T.ptN2 1 A'.s (fun _ => A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) / A'.T.l2 1 A'.s = A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s ∧ ∀ u ∈ X.Λ, A.T.ptN2 1 A.s (fun _ => A.φ (v + u)) / A.T.l2 1 A.s = A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s := by sorry
