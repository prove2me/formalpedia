-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_integral_compactApprox_tendsto
-- name    : OAI.DiagonalForms.System.integral_compactApprox_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:25:13.573205+00:00
-- url     : https://prove2.me/theorems/7a8263a9-a695-4cb3-991f-2565cdd5c481
-- title:
--   Integrals along simple-function approximations of the identity on a compact metric space converge
-- statement:
--   Let $K$ be a compact metric space with its Borel $\sigma$-algebra, $\mu$ a finite measure on $K$, and $k_0 \in K$. Let $(d_m)_{m \ge 0}$ be the fixed dense sequence of $K$ used by Mathlib, and for $n \in \mathbb{N}$ let $A_n : K \to K$ be the simple function sending $k$ to a point of $\{k_0, d_0, \dots, d_{n-1}\}$ nearest to $k$ (ties broken in favour of the earlier point). This is Mathlib's standard approximation of the identity map of $K$ by simple functions.
--
--   **Theorem.** For every continuous $g : K \to \mathbb{R}$,
--   $$
--   \lim_{n \to \infty} \int_K g\big(A_n(k)\big)\, d\mu(k) = \int_K g(k)\, d\mu(k).
--   $$
--
--   Combined with the formula for integrals of functions of simple functions, this lets one approximate an integral over the compact parameter space $K$ by finite weighted sums $\sum_k \mu(A_n^{-1}(\{k\}))\,g(k)$; it is used to pass properties of finite sums of comparison weights to integrals.
--
--   **Formalization Note** $A_n$ is `compactApprox k₀ n = SimpleFunc.approxOn id measurable_id Set.univ k₀ _ n`; the integrals are Bochner integrals and convergence is along `atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L477-L489

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
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

theorem OAI.DiagonalForms.System.integral_compactApprox_tendsto {g : K → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ k, g (compactApprox k₀ n k) ∂μ) atTop (𝓝 (∫ k, g k ∂μ)) := by sorry
