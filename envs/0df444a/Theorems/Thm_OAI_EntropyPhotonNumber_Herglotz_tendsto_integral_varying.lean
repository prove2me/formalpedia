-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_tendsto_integral_varying
-- name    : OAI.EntropyPhotonNumber.Herglotz.tendsto_integral_varying
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:11.437982+00:00
-- url     : https://prove2.me/theorems/e75e2066-5296-499d-a7df-9a16c6f48585
-- title:
--   Integrals converge when both the measure (weakly) and the continuous integrand (uniformly) converge
-- statement:
--   Let $X$ be a compact topological space equipped with its Borel $\sigma$-algebra. Let $l$ be a filter on an index set $\iota$. Let $(\mu_i)_{i\in\iota}$ be finite Borel measures on $X$ converging along $l$ to a finite measure $\mu$ in the weak topology of finite measures, i.e. $\int g\,d\mu_i\to\int g\,d\mu$ for every bounded continuous $g$. Let $(f_i)_{i\in\iota}$ be continuous real functions on $X$ converging along $l$ to $f$ in $C(X,\mathbb{R})$, i.e. uniformly on $X$. Then
--   $$
--   \lim_{i\to l}\int_Xf_i\,d\mu_i=\int_Xf\,d\mu .
--   $$
--
--   So integration $(\mu,f)\mapsto\int f\,d\mu$ is jointly continuous for weak convergence of measures and uniform convergence of integrands on a compact space. In the Herglotz-representation argument it is used to pass to the limit in Poisson-type integrals when both the radial measures and the kernels change.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L56-L80

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Herglotz
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
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

theorem OAI.EntropyPhotonNumber.Herglotz.tendsto_integral_varying {ι : Type*} {l : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    {fs : ι → C(X, ℝ)} {f : C(X, ℝ)}
    (hμ : Tendsto μs l (𝓝 μ)) (hf : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by sorry
