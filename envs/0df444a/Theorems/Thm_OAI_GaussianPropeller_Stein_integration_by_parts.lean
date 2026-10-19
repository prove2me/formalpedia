-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Stein_integration_by_parts
-- name    : OAI.GaussianPropeller.Stein.integration_by_parts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:02:38.782493+00:00
-- url     : https://prove2.me/theorems/9059ddf3-c41b-4a57-b54a-ad09bf60cce2
-- title:
--   Gaussian integration by parts
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $E=\mathbb R^\iota$. Let $H:E\to\mathbb R$ be bounded and differentiable, with continuous bounded derivative $DH$. Then for every $v\in E$,
--   $$
--   \int DH(x)\,v\,d\gamma(x)=\int H(x)\,\langle v,x\rangle\,d\gamma(x).
--   $$
--
--   This is Stein's identity, the basic tool for differentiating Gaussian expectations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Stein.lean#L67-L103

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation

open OAI OAI.GaussianPropeller
universe uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open GaussianPropeller.Translation
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

theorem OAI.GaussianPropeller.Stein.integration_by_parts {H : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt H (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C) (v : E) :
    ∫ x, D x v ∂γ = ∫ x, H x*⟪v,x⟫ ∂γ := by sorry
