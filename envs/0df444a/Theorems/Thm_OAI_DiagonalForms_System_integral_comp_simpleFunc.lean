-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_integral_comp_simpleFunc
-- name    : OAI.DiagonalForms.System.integral_comp_simpleFunc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:24:37.114089+00:00
-- url     : https://prove2.me/theorems/ef7652fc-f818-4a98-8cfe-daafbf460e89
-- title:
--   Integral of a function of a simple function as a finite sum over its values
-- statement:
--   Let $(X, \mathcal A)$ be a measurable space carrying a finite measure $\mu$, let $K$ be any type, let $f : X \to K$ be a simple function (measurable fibres $f^{-1}(\{k\})$ and finitely many values), and let $g : K \to \mathbb{R}$ be an arbitrary function.
--
--   **Theorem.**
--   $$
--   \int_X g(f(x))\,d\mu(x) = \sum_{k \in f(X)} \mu\big(f^{-1}(\{k\})\big)\, g(k).
--   $$
--
--   The identity converts an integral of a quantity depending on a parameter only through a simple approximation into a finite weighted sum with nonnegative weights $\mu(f^{-1}(\{k\}))$. In the comparison-weight calculus this is how integrals over a compact parameter space are reduced, at each approximation step, to finite harmonic sums.
--
--   **Formalization Note** The integral is the Bochner integral, $f$ is a `MeasureTheory.SimpleFunc X K`, the index set is the finset `f.range`, and $\mu(\cdot)$ is `μ.real`, the measure converted to a real number (finite because `IsFiniteMeasure μ`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L419-L433

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

open OAI OAI.DiagonalForms OAI.DiagonalForms.System
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
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem OAI.DiagonalForms.System.integral_comp_simpleFunc {X K : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : MeasureTheory.SimpleFunc X K) (g : K → ℝ) :
    (∫ x, g (f x) ∂μ) = ∑ k ∈ f.range, μ.real (f ⁻¹' {k}) * g k := by sorry
