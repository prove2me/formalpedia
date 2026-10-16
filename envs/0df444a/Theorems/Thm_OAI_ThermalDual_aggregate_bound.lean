-- Prove2me | Theorems.Thm_OAI_ThermalDual_aggregate_bound
-- name    : OAI.ThermalDual.aggregate_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:49:19.943775+00:00
-- url     : https://prove2.me/theorems/84981c75-bf46-4bc2-94bc-8a3a10cfd084
-- title:
--   Aggregating per-mode defect bounds into an $\ell^2$ bound over modes
-- statement:
--   Let $I$ and $J$ be finite sets. Let $w_i\ge0$ $(i\in I)$, let $q^0_j\ge0$ and $g_j\ge0$ $(j\in J)$, let $q_{ij},m_{ij}\in\mathbb{R}$, let $C\ge0$ and $\kappa\in[0,1]$. Assume for every $j\in J$
--   $$(1-\kappa)\,g_j^2\le2\sum_{i}w_i\,m_{ij}^2\qquad\text{and}\qquad q^0_j\le\sqrt{\sum_iw_i\,q_{ij}^2}+\sqrt{(1-\kappa)\kappa}\;g_j\,C .$$
--   Then
--   $$\sqrt{\sum_{j}(q^0_j)^2}\le\sqrt{\sum_iw_i\sum_jq_{ij}^2}+\sqrt{2\kappa}\;C\,\sqrt{\sum_iw_i\sum_jm_{ij}^2}.$$
--
--   Here $j$ indexes modes: per-mode bounds for an output defect $q^0_j$ in terms of input defects $q_{ij}$, plus a mixing error controlled by auxiliary quantities $m_{ij}$, are combined into a single bound for the total ($\ell^2$ over modes) defect.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Duality.lean#L471-L510

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality

open OAI
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory
variable {I J : Type*} [Fintype I] [Fintype J]

theorem OAI.ThermalDual.aggregate_bound (w : I → ℝ) (hw : ∀ i, 0≤w i)
    (q0 g : J → ℝ) (q m : I → J → ℝ) (hq : ∀ j, 0≤q0 j)
    (hg : ∀ j, 0≤g j) (C κ : ℝ) (hC : 0≤C) (hκ : κ ∈ Set.Icc 0 1)
    (hm : ∀ j, (1-κ)*g j^2≤2*∑ i, w i*m i j^2)
    (hmode : ∀ j, q0 j≤Real.sqrt (∑ i, w i*q i j^2)+Real.sqrt ((1-κ)*κ)*g j*C) :
    Real.sqrt (∑ j, q0 j^2)≤Real.sqrt (∑ i, w i*∑ j, q i j^2)+
      Real.sqrt (2*κ)*C*Real.sqrt (∑ i, w i*∑ j, m i j^2) := by sorry
