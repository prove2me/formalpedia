-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactIntegral_ne_zero
-- name    : OAI.EntropyPhotonNumber.Herglotz.compactIntegral_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:17:00.045426+00:00
-- url     : https://prove2.me/theorems/08992c83-6dd5-4a49-861b-d1bf3d92ab92
-- title:
--   The compact Stieltjes-type integral $K_\mu$ has no zeros in the upper half-plane
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
--   **Theorem.** If $\mu$ is a finite Borel measure on $\Theta$ with $\mu\neq0$, then
--   $$
--   K_\mu(s)\neq0\qquad\text{for every }s\in\mathbb{C}\text{ with }\operatorname{Im}s>0 .
--   $$
--
--   This makes $1/(s\,K_\mu(s))$ holomorphic on the upper half-plane. That reciprocal is the function whose Stieltjes representation produces the positive weight in the interpolation argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L948-L980

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

theorem OAI.EntropyPhotonNumber.Herglotz.compactIntegral_ne_zero (μ : FiniteMeasure Angle)
    (hμ : (μ : Measure Angle) ≠ 0) {s : ℂ} (hs : 0 < s.im) : compactIntegral μ s ≠ 0 := by sorry
