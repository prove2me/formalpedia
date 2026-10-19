-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_HeatMaximum_heat_concave
-- name    : OAI.GaussianPropeller.HeatMaximum.heat_concave
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:10:35.64116+00:00
-- url     : https://prove2.me/theorems/5bfcf34f-40e2-4f87-810b-77f8de85ee0d
-- title:
--   A maximum principle preserving concavity
-- statement:
--   Let $E$ be a finite-dimensional inner product space with an orthonormal family $(b_i)$, and let $v_t$, $0\le t\le T$, be continuous in $(t,x)$ with $v_0$ concave. Suppose that for $0<t\le T$:
--
--   - $v_t$ has gradient $p_t$ with $|p_t|\le L$;
--   - $H_t(x,e)$ is the derivative of $\langle p_t(x+se),e\rangle$ at $s=0$;
--   - $|v_t(x)|\le M+L|x|$ on $[0,T]$;
--   - $v$ evolves by the equation below.
--
--   $$
--   \partial_tv_t(x)=\frac12\Bigl(\sum_iH_t(x,b_i)-v_t(x)\,|p_t(x)|^2\Bigr).
--   $$
--
--   Then $v_T$ is concave. This is the evolution equation satisfied by $\Phi^{-1}$ of a heat flow, which is the analytic core of Ehrhard's inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/HeatMaximum.lean#L416-L450

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatMaximum
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
open Set Filter
open scoped Topology RealInnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.GaussianPropeller.HeatMaximum.heat_concave [ProperSpace E] {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : ℝ → E → E} {H : ℝ → E → E → ℝ}
    {T L M : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : Continuous (fun q : ℝ × E => v q.1 q.2))
    (hinitial : ConcaveOn ℝ univ (v 0))
    (hp : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v t) (innerSL ℝ (p t x)) x)
    (hH : ∀ t ∈ Ioc 0 T, ∀ x e, HasDerivAt (fun s : ℝ => ⟪p t (x+s • e),e⟫) (H t x e) 0)
    (hvt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H t x (basis i))-v t x*‖p t x‖^2)/2) t)
    (hpbound : ∀ t ∈ Ioc 0 T, ∀ x, ‖p t x‖ ≤ L)
    (hvbound : ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M+L*‖x‖) :
    ConcaveOn ℝ univ (v T) := by sorry
