-- Prove2me | Theorems.Thm_OAI_QuantumTrace_negativeLog_form_mono
-- name    : OAI.QuantumTrace.negativeLog_form_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:09.699788+00:00
-- url     : https://prove2.me/theorems/535740e9-873a-4ba6-88f4-5a6521b7e61e
-- title:
--   Quadratic-form monotonicity of $-\log$ for positive operators with eigenbases
-- statement:
--   Let $E$ be a complex Hilbert space and let $T,R$ be positive bounded operators on $E$ with $R\le T$ (that is, $T-R$ is positive). Suppose $T$ has a Hilbert (orthonormal) eigenbasis $(b_i)_{i\in I}$ with $Tb_i=p_ib_i$ and $R$ has a Hilbert eigenbasis $(c_j)_{j\in J}$ with $Rc_j=q_jc_j$, where $0<p_i\le1$ and $0<q_j\le1$ for all $i,j$. Let $x\in E$ be such that the series $\sum_j(-\log q_j)\,|\langle c_j,x\rangle|^2$ converges. Then the series $\sum_i(-\log p_i)\,|\langle b_i,x\rangle|^2$ also converges, and
--
--   $$
--   \sum_{i\in I}(-\log p_i)\,|\langle b_i,x\rangle|^2\;\le\;\sum_{j\in J}(-\log q_j)\,|\langle c_j,x\rangle|^2 .
--   $$
--
--   The two sides are the quadratic forms $\langle x,(-\log T)x\rangle$ and $\langle x,(-\log R)x\rangle$ of the possibly unbounded operators $-\log T$ and $-\log R$, computed in their eigenbases. The statement is therefore the operator monotonicity of the logarithm, $R\le T\Rightarrow-\log T\le-\log R$, in a form-domain version that needs no unbounded functional calculus. It is used to compare $-\log\rho$ with $-\log$ of a multiple of a thermal state.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean#L553-L609

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

open OAI OAI.QuantumTrace
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
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

theorem OAI.QuantumTrace.negativeLog_form_mono (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    {T R : E →L[ℂ] E} (hT : T.IsPositive) (hR : R.IsPositive) (hRT : R ≤ T)
    (p : I → ℝ) (q : J → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hp1 : ∀ i, p i ≤ 1) (hq1 : ∀ j, q j ≤ 1)
    (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
    (heR : ∀ j, R (c j) = (q j : ℂ) • c j) (x : E)
    (hfin : Summable (fun j => -Real.log (q j)*‖inner ℂ (c j) x‖^2)) :
    Summable (fun i => -Real.log (p i)*‖inner ℂ (b i) x‖^2) ∧
      (∑' i, -Real.log (p i)*‖inner ℂ (b i) x‖^2) ≤
        ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by sorry
