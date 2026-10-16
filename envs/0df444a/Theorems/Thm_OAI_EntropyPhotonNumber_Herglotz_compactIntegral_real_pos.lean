-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactIntegral_real_pos
-- name    : OAI.EntropyPhotonNumber.Herglotz.compactIntegral_real_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:19:29.709787+00:00
-- url     : https://prove2.me/theorems/dd4510a9-96e5-4f46-a9df-8351d15395f7
-- title:
--   The compact Stieltjes-type integral $K_\mu$ is positive on the positive real axis
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
--   **Theorem.** If $\mu$ is a finite Borel measure on $\Theta$ with $\mu\ne0$ and $x>0$ is real, then
--   $$
--   \operatorname{Re}K_\mu(x)>0 .
--   $$
--
--   For real $x>0$, $K_\mu(x)$ is real, so this says $K_\mu(x)>0$. Consequently $1/(xK_\mu(x))$ is a well-defined positive real number. This is the positivity on the boundary needed to apply the Stieltjes-type representation to that reciprocal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L1305-L1317

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

theorem OAI.EntropyPhotonNumber.Herglotz.compactIntegral_real_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < (compactIntegral μ (x : ℂ)).re := by sorry
