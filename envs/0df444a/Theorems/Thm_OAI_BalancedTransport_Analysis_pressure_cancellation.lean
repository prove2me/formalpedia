-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Analysis_pressure_cancellation
-- name    : OAI.BalancedTransport.Analysis.pressure_cancellation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:28:13.147548+00:00
-- url     : https://prove2.me/theorems/2ca3b4c3-dbea-46f1-a159-05dc44eb564d
-- title:
--   A pressure gradient is orthogonal to divergence-free fields
-- statement:
--   Let $w:\mathbb R^3\to\mathbb R^3$ be $C^\infty$ and divergence free, with $w_j$ and $\partial_jw_j$ square integrable. Let $p:\mathbb R^3\to\mathbb R$ be $C^\infty$ with $p$ and $\partial_jp$ square integrable. Then
--   $$
--   \sum_{j=0}^2\int_{\mathbb R^3}w_j\,\partial_jp\,dx=0 .
--   $$
--
--   So the pressure drops out of the energy identity for the difference of two solutions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Energy.lean#L117-L139

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.BalancedTransport.Analysis.pressure_cancellation {w : Space → Space} {p : Space → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hdiv : ∀ x, ∑ j, pd j w x j = 0)
    (hw₂ : ∀ j, MemLp (fun x => w x j) 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (fun x => pd j w x j) 2 (volume : Measure Space))
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hdp₂ : ∀ j, MemLp (pd j p) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, w x j * pd j p x) = 0 := by sorry
