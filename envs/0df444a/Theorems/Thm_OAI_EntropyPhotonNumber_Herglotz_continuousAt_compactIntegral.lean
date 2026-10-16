-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_continuousAt_compactIntegral
-- name    : OAI.EntropyPhotonNumber.Herglotz.continuousAt_compactIntegral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:17:37.248814+00:00
-- url     : https://prove2.me/theorems/b8c85d98-b43e-48e9-ba34-08bf84216f20
-- title:
--   Continuity of the compact Stieltjes-type integral $K_\mu$ on the right half-plane
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
--   **Theorem.** For every finite Borel measure $\mu$ on $\Theta$ and every $s\in\mathbb{C}$ with $\operatorname{Re}s>0$, the function $K_\mu:\mathbb{C}\to\mathbb{C}$ is continuous at $s$.
--
--   Continuity up to the positive real axis lets identities between $K_\mu$ and other functions, first proved on the upper half-plane, be extended to real points $x>0$ by approaching them from above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L982-L1012

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

theorem OAI.EntropyPhotonNumber.Herglotz.continuousAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (compactIntegral μ) s := by sorry
