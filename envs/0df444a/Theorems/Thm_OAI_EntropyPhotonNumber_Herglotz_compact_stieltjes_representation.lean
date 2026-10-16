-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compact_stieltjes_representation
-- name    : OAI.EntropyPhotonNumber.Herglotz.compact_stieltjes_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:18:20.893626+00:00
-- url     : https://prove2.me/theorems/0a491fe1-3725-414f-ad07-ecd35d496047
-- title:
--   Compact Stieltjes-type representation on $(0,\infty)$ of functions with $\operatorname{Im}R\le0$ on the upper half-plane
-- statement:
--   Let $\Theta=[0,2\pi]$ with its Borel $\sigma$-algebra and, for $\theta\in\Theta$, let $\zeta_\theta=e^{i\theta}$, $h_\theta=\max(0,\operatorname{Im}\zeta_\theta)$ and
--   $$
--   t(\theta)=\frac{1-\operatorname{Re}\zeta_\theta+h_\theta}{2(1+h_\theta)}\in[0,1].
--   $$
--
--   **Theorem.** Let $R:\mathbb{C}\to\mathbb{C}$ be holomorphic on the open upper half-plane $\mathbb{H}$ with $\operatorname{Im}R(s)\le0$ there. Assume that for every real $x>0$, $R$ is complex-analytic at $x$, $R(x)$ is real and $R(x)\ge0$. Then there are a constant $c\ge0$ and a finite Borel measure $\nu$ on $\Theta$ such that
--   $$
--   \operatorname{Re}R(x)=c+\int_\Theta\frac{d\nu(\theta)}{1+(x-1)\,t(\theta)}\qquad\text{for all real }x>0 .
--   $$
--
--   Since $t(\theta)\in[0,1]$, the right side is a nonnegative constant plus a positive mixture of the functions $x\mapsto1/(1+(x-1)t)=1/((1-t)+tx)$. This is a Stieltjes-type representation on the positive half-line with a compactly parametrized family of kernels. It is applied to the reciprocal function $1/(sK_\mu(s))$ to show that the weight function in the interpolation argument is continuous and positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L1188-L1209

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

theorem OAI.EntropyPhotonNumber.Herglotz.compact_stieltjes_representation {R : ℂ → ℂ}
    (hR : AnalyticOnNhd ℂ R {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → (R s).im ≤ 0)
    (hp : ∀ x : ℝ, 0 < x → AnalyticAt ℂ R (x : ℂ) ∧ (R (x : ℂ)).im = 0 ∧ 0 ≤ (R (x : ℂ)).re) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → (R (x : ℂ)).re = c +
        ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by sorry
