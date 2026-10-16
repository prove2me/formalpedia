-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_differentiableAt_compactIntegral
-- name    : OAI.EntropyPhotonNumber.Herglotz.differentiableAt_compactIntegral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:18:58.903867+00:00
-- url     : https://prove2.me/theorems/1533b369-67fe-45a5-a8fe-72a00988c7ec
-- title:
--   Complex differentiability of $K_\mu$ on the upper and right half-planes
-- statement:
--   **Notation.** Let $\Theta=[0,2\pi]$ with its Borel $\sigma$-algebra, and for $\theta\in\Theta$ write $\zeta_\theta=e^{i\theta}$ and $h_\theta=\max(0,\operatorname{Im}\zeta_\theta)$. Define the continuous functions
--   $$
--   t(\theta)=\frac{1-\operatorname{Re}\zeta_\theta+h_\theta}{2(1+h_\theta)}\in[0,1],\qquad w(\theta)=\frac{1}{1+h_\theta}\in(0,1].
--   $$
--   For a finite Borel measure $\mu$ on $\Theta$ and $s\in\mathbb{C}$ put
--   $$
--   K_\mu(s)=\int_\Theta\frac{w(\theta)}{1+(s-1)\,t(\theta)}\,d\mu(\theta).
--   $$
--
--   **Theorem.** For every finite Borel measure $\mu$ on $\Theta$ and every $s\in\mathbb{C}$ with $\operatorname{Im}s>0$ or $\operatorname{Re}s>0$, the function $K_\mu$ is complex differentiable at $s$.
--
--   Hence $K_\mu$ is holomorphic on the union of the open upper and right half-planes. This is what allows the resolvent functions built from $K_\mu$ to be treated as analytic functions, for example in identity-theorem arguments on the right half-plane.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L1248-L1292

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
attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle

theorem OAI.EntropyPhotonNumber.Herglotz.differentiableAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : DifferentiableAt ℂ (compactIntegral μ) s := by sorry
