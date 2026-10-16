-- Prove2me | Theorems.Thm_OAI_QuantumTrace_spectral_form_representation
-- name    : OAI.QuantumTrace.spectral_form_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:44:31.183444+00:00
-- url     : https://prove2.me/theorems/73ed76cc-98dd-4c9a-a404-d585f978b9e9
-- title:
--   Positive operator representing a spectrally weighted quadratic form
-- statement:
--   Let $E$ be a complex Hilbert space with a Hilbert (orthonormal) basis $(b_j)_{j\in J}$, let $c:J\to\mathbb R$ with $c_j\ge0$ for all $j$, and let $V$ be a bounded symmetric operator on $E$. Assume that for every $y\in E$ the series $\sum_jc_j|\langle b_j,Vy\rangle|^2$ converges, and that there is a constant $C\ge0$ with
--   $\sum_jc_j|\langle b_j,Vy\rangle|^2\le C\|y\|^2$ for all $y$. Then there exists a positive bounded operator $B$ on $E$ such that
--
--   1. for every $y\in E$,
--   $$
--   \sum_{j\in J}c_j\,|\langle b_j,Vy\rangle|^2=\operatorname{Re}\langle y,By\rangle ,
--   $$
--   with the series converging to the right-hand side;
--   2. for every $j\in J$, $y\in E$ and $z\in\mathbb C$: if $Vy=z\,b_j$, then $By=c_j\,V(z\,b_j)$.
--
--   Formally $B=V\big(\sum_jc_j|b_j\rangle\langle b_j|\big)V$, but the diagonal operator in the middle may be unbounded; the theorem produces a bounded positive representative from the form bound alone. With $c_j=-\log p_j$ for the eigenvalues $p_j$ of a state and a smoothing operator $V$, it provides a bounded "sandwiched logarithm" of the state, and property 2 identifies how $B$ acts on preimages of eigenvectors.
--
--   **Formalization Note** Positivity is Mathlib's `IsPositive` for continuous linear maps; the operator constructed is the Gram operator $A^*A$ of the analysis map $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean#L107-L150

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
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

theorem OAI.QuantumTrace.spectral_form_representation (b : HilbertBasis J ℂ E) (c : J → ℝ)
    (hc : ∀ j, 0≤c j) (V : E →L[ℂ] E) (hV : V.IsSymmetric)
    (hs : ∀ y, Summable (fun j => c j*‖inner ℂ (b j) (V y)‖^2))
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ y, (∑' j, c j*‖inner ℂ (b j) (V y)‖^2)≤C*‖y‖^2) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧
      (∀ y, HasSum (fun j => c j*‖inner ℂ (b j) (V y)‖^2) (inner ℂ y (B y)).re) ∧
      ∀ (j : J) (y : E) (z : ℂ), V y=z • b j → B y=(c j:ℂ) • V (z • b j) := by sorry
