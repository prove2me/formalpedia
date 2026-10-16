-- Prove2me | Theorems.Thm_OAI_QuantumCalculus_log_partition_expansion
-- name    : OAI.QuantumCalculus.log_partition_expansion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:38:17.250004+00:00
-- url     : https://prove2.me/theorems/3e54fd3d-b056-4c51-8b81-0e2091bbf341
-- title:
--   Second-order expansion of a log-partition function in a Banach algebra with a trace
-- statement:
--   Let $A$ be a real Banach algebra (a complete normed ring that is a normed $\mathbb{R}$-algebra) and let $\tau:A\to\mathbb{R}$ be a continuous $\mathbb{R}$-linear functional with the trace property $\tau(xy)=\tau(yx)$ for all $x,y\in A$. Let $a,z\in A$ and $c\in\mathbb{R}$ satisfy the normalization
--   $$c+\tau(e^{a})=1 .$$
--   Then, as $t\to0$,
--   $$\log\bigl(c+\tau(e^{a+tz})\bigr)-\tau(e^{a}z)\,t-\frac{1}{2}\Bigl(\tau\Bigl[\Bigl(\int_0^1e^{(1-s)a}\,z\,e^{sa}\,ds\Bigr)z\Bigr]-\tau(e^{a}z)^2\Bigr)t^2=o(t^2).$$
--
--   This is the second-order Taylor expansion of the (shifted) log-partition function $t\mapsto\log(c+\tau(e^{a+tz}))$: the first derivative is the mean $\tau(e^az)$ and the second derivative is the Duhamel (Kubo–Mori) second moment minus the squared mean, i.e. a variance. The constant $c$ allows part of the normalization to come from a component of the state that is not perturbed.
--
--   **Formalization Note** $o(t^2)$ is Mathlib's little-o (`=o[𝓝 0]`); $e^{x}$ is `NormedSpace.exp` and the integral is a Bochner interval integral in $A$. A local instance regards $A$ as a normed $\mathbb{Q}$-algebra, needed for the exponential.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L1099-L1123

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation

open OAI OAI.QuantumCalculus
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_2

theorem OAI.QuantumCalculus.log_partition_expansion (τ : A →L[ℝ] ℝ)
    (hτ : ∀ x y, τ (x*y) = τ (y*x)) (a z : A) (c : ℝ)
    (hn : c+τ (exp a) = 1) :
    (fun t : ℝ => Real.log (c+τ (exp (a+t • z))) -
      τ (exp a*z)*t -
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z) -
        (τ (exp a*z))^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by sorry
