-- Prove2me | Theorems.Thm_OAI_IndependentProducts_midpointGain_eq_integral_excess
-- name    : OAI.IndependentProducts.midpointGain_eq_integral_excess
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:28:01.184241+00:00
-- url     : https://prove2.me/theorems/0e86b1fd-47a8-4cef-b162-3f6fff5d7187
-- title:
--   The $L^1$ midpoint gain as an integral of pointwise excess
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a measure space and let $x,y\in L^1(P)$ be real-valued integrable classes. Let $f,g:\Omega\to\mathbb R$ be functions with $x=f$ and $y=g$ $P$-almost everywhere, and let $t\ge0$. Then
--
--   $$
--   \frac{\|x+ty\|_{1}+\|x-ty\|_{1}}{2}-\|x\|_{1}=\int_\Omega\max\big(t\,|g(\omega)|-|f(\omega)|,\;0\big)\,dP(\omega).
--   $$
--
--   The left-hand side is the midpoint gain $\Delta_t(x,y)$ of the $L^1$ norm. The theorem identifies it with the integral of the pointwise excess $\mathrm{ex}_t(r,z)=\max(t|z|-r,0)$ evaluated at $r=|f(\omega)|$ and $z=g(\omega)$: the gain comes exactly from the region where the perturbation $t|y|$ dominates the center $|x|$. This converts estimates for the midpoint modulus of subspaces of $L^1$ into estimates for integrals of a nonnegative function.
--
--   **Formalization Note** The left-hand side is `midpointGain t x y` and the integrand is `excess t |f ω| (g ω)` with `excess t r z = max (t * |z| - r) 0`. The measure $P$ is arbitrary (no finiteness assumption), and $f,g$ are only assumed to agree almost everywhere with $x,y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ConditionalBounds.lean#L78-L113

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΛ uΩ uι

theorem OAI.IndependentProducts.midpointGain_eq_integral_excess {Ω : Type uΩ} [MeasurableSpace Ω] (P : Measure Ω)
    (x y : Lp ℝ 1 P) (f g : Ω → ℝ) (hf : x =ᵐ[P] f) (hg : y =ᵐ[P] g)
    (t : ℝ) (ht : 0 ≤ t) :
    midpointGain t x y = ∫ ω, excess t |f ω| (g ω) ∂P := by sorry
