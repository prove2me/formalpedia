-- Prove2me | Theorems.Thm_OAI_BKM_finite_hessian_to_variance
-- name    : OAI.BKM.finite_hessian_to_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:23:28.778119+00:00
-- url     : https://prove2.me/theorems/d31a86f4-adf4-4ca8-b3a5-5ef77c11c503
-- title:
--   From finite-section quadratic inequalities to a variance bound
-- statement:
--   Let $J$ be an arbitrary index set. Let $v : J\times J\to\mathbb{R}$ and $m : J\to\mathbb{R}$ be unconditionally summable families with
--   $$\sum_{(i,j)\in J\times J} v(i,j)=A,\qquad \sum_{i\in J} m(i)=\mu ,$$
--   and let $\alpha,\gamma,W$ be real numbers with $\alpha>0$. For a finite set $s\subseteq J$ write
--   $$V_s=\sum_{i\in s}\sum_{j\in s} v(i,j),\qquad M_s=\sum_{i\in s} m(i).$$
--   Assume that for every finite set $s\subseteq J$ and every real number $t$
--   $$2\gamma t\,\bigl(V_s-\mu M_s\bigr)\;\le\;\alpha t^{2}\,\bigl(V_s-M_s^{2}\bigr)+W .$$
--   Then
--   $$\gamma^{2}\,\bigl(A-\mu^{2}\bigr)\;\le\;\alpha W .$$
--
--   In applications $A-\mu^2$ is a variance-type quantity (a second moment minus the square of a mean), and the hypothesis is a second-order inequality along a one-parameter perturbation $t$ that is only available on finite truncations $s$ of an infinite index set. The lemma passes to the limit along the truncations and optimizes over $t$, turning such a Hessian-type estimate into a bound on the variance.
--
--   **Formalization Note** Summability is expressed with `HasSum`, i.e. unconditional convergence of the real series; the truncations are indexed by `Finset J`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralForms.lean#L116-L133

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms

open OAI OAI.BKM
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open scoped BigOperators
variable {J : Type*}

theorem OAI.BKM.finite_hessian_to_variance (v : J × J → ℝ) (m : J → ℝ) (μ A α γ W : ℝ)
    (hv : HasSum v A) (hm : HasSum m μ) (hα : 0 < α)
    (h : ∀ (s : Finset J) (t : ℝ),
      2*γ*t*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-μ*(∑ i ∈ s, m i)) ≤
        α*t^2*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-(∑ i ∈ s, m i)^2)+W) :
    γ^2*(A-μ^2) ≤ α*W := by sorry
