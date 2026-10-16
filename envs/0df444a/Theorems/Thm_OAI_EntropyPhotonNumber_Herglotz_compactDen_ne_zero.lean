-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactDen_ne_zero
-- name    : OAI.EntropyPhotonNumber.Herglotz.compactDen_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:47.08565+00:00
-- url     : https://prove2.me/theorems/1255efdd-64e9-4ecc-acbd-61df54a4b43d
-- title:
--   The denominator $1+(s-1)t$ has no zero for $t\in[0,1]$ when $\operatorname{Im}s>0$ or $\operatorname{Re}s>0$
-- statement:
--   Let $t\in[0,1]$ and let $s\in\mathbb{C}$ satisfy $\operatorname{Im}s>0$ or $\operatorname{Re}s>0$. Then
--   $$
--   1+(s-1)\,t\neq0 .
--   $$
--
--   The expression $1+(s-1)t=(1-t)+ts$ is the convex combination of $1$ and $s$ with weight $t$, so the statement says that the segment from $1$ to $s$ avoids $0$ when $s$ lies in the open upper half-plane or the open right half-plane. It guarantees that the kernels $w/(1+(s-1)t)$ used in the compact Stieltjes-type representations are well defined, bounded and continuous on these regions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean#L743-L759

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

theorem OAI.EntropyPhotonNumber.Herglotz.compactDen_ne_zero {t : ℝ} (ht : t ∈ Icc 0 1) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : 1 + (s - 1) * (t : ℂ) ≠ 0 := by sorry
