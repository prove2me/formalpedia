-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Analysis_energy_pairing_bound
-- name    : OAI.BalancedTransport.Analysis.energy_pairing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:30:44.192461+00:00
-- url     : https://prove2.me/theorems/edee5a5e-c204-4431-8b0d-a360bf08e948
-- title:
--   Energy pairing estimate for the difference of two solutions
-- statement:
--   A vector field $w:\mathbb R^3\to\mathbb R^3$ is in the slice class when it is $C^\infty$ and all components $w_i$, all first partial derivatives $\partial_jw_i$ and all pure second derivatives $\partial_j^2w_i$ are square integrable. Let $w$ be in the slice class and divergence free. Let $a$ be $C^\infty$ and divergence free with $|a|\le A$ and $|\partial_ja|\le A$. Let $v$ be $C^\infty$ with $|\partial_jv|\le C$, where $C\ge0$. Let $p$ be $C^\infty$ with $p$ and $\partial_jp$ square integrable, and let $\nu\ge0$. If
--   $$
--   g_i=\nu\,\Delta w_i-(a\cdot\nabla)w_i-(w\cdot\nabla)v_i-\partial_ip\qquad(i=0,1,2),
--   $$
--   then
--   $$
--   \sum_i\int w_i\,g_i\,dx\le6C\sum_i\int w_i^2\,dx .
--   $$
--
--   For $w=u-U$, $a=u$ and $v=U$, $g$ is $\partial_tw$ by the difference of the two Navier–Stokes equations. So the estimate bounds the growth of the energy of $w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergySlice.lean#L82-L175

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

theorem OAI.BalancedTransport.Analysis.energy_pairing_bound
    {w a v g : Space → Space} {p : Space → ℝ} {ν C A : ℝ}
    (hw : SliceH2 w) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (ha_b : ∀ x, ‖a x‖ ≤ A) (ha_d : ∀ x j, ‖pd j a x‖ ≤ A)
    (hv_d : ∀ x j, ‖pd j v x‖ ≤ C)
    (ha_div : ∀ x, ∑ j, pd j a x j = 0)
    (hw_div : ∀ x, ∑ j, pd j w x j = 0)
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hp_d : ∀ j, MemLp (pd j p) 2 (volume : Measure Space))
    (hPDE : ∀ x i, g x i = ν * (∑ j, pd j (pd j w) x i) -
      (∑ j, a x j * pd j w x i) - (∑ j, w x j * pd j v x i) - pd i p x) :
    (∑ i : Fin 3, ∫ x, w x i * g x i) ≤
      6 * C * (∑ i : Fin 3, ∫ x, (w x i)^2) := by sorry
