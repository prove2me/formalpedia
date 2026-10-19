-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_QuantilePDE_quantile_gradient_line_derivative
-- name    : OAI.GaussianPropeller.QuantilePDE.quantile_gradient_line_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:08:08.321998+00:00
-- url     : https://prove2.me/theorems/1bf7a8b5-2401-48a1-9e18-d2175515ea70
-- title:
--   Second directional derivative of a Gaussian quantile
-- statement:
--   Let $\varphi$ and $\Phi$ be the standard normal density and distribution function, and $q=\Phi^{-1}$ on $(0,1)$. Let $u:E\to(0,1)$ have gradient $g$ and $g$ have derivative $K$, and put $v=q\circ u$. The gradient of $v$ is $g/\varphi(v)$. Along a line $x+se$, its component in direction $e$ has derivative at $s=0$
--   $$
--   \frac{\langle K(x)e,e\rangle}{\varphi(v(x))}+v(x)\,\frac{\langle g(x),e\rangle^2}{\varphi(v(x))^2}.
--   $$
--
--   This is the second derivative of $v$ in direction $e$; the second term comes from $\varphi'(t)=-t\varphi(t)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/QuantileCalculus.lean#L30-L53

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus

open OAI OAI.GaussianPropeller
universe uE uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.GaussianPropeller.QuantilePDE.quantile_gradient_line_derivative {u : E → ℝ} {g : E → E}
    {K : E → E →L[ℝ] E} (hu : ∀ x, u x ∈ Ioo (0:ℝ) 1)
    (hdu : ∀ x, HasFDerivAt u (innerSL ℝ (g x)) x)
    (hdg : ∀ x, HasFDerivAt g (K x) x) (x e : E) :
    HasDerivAt (fun s : ℝ => ⟪(φ (q (u (x+s•e))))⁻¹ • g (x+s•e), e⟫)
      ((φ (q (u x)))⁻¹*⟪K x e,e⟫ +
        q (u x)*(φ (q (u x)))⁻¹^2*⟪g x,e⟫^2) 0 := by sorry
