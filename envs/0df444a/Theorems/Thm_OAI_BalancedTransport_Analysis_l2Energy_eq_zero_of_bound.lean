-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Analysis_l2Energy_eq_zero_of_bound
-- name    : OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:26:13.506737+00:00
-- url     : https://prove2.me/theorems/7edb0b87-ae50-4480-a0b1-49a87c3c0a44
-- title:
--   Energy that starts at zero and grows at most linearly stays zero
-- statement:
--   For $V\in L^2(\mathbb R^3;\mathbb R^3)$ let $\mathcal E(V)=\sum_i\|V_i\|_{L^2}^2$, and for $V,W\in L^2$ let $\mathcal E'(V;W)=2\sum_i\langle V_i,W_i\rangle_{L^2}$, the rate of change of the energy along a curve with velocity $W$. Let $V:[0,\infty)\to L^2(\mathbb R^3;\mathbb R^3)$ be continuous with right derivative $W(t)$ at each $t\ge0$, and $V(0)=0$. Let $T\ge0$ and $K\in\mathbb R$, and suppose
--   $$
--   \mathcal E'\bigl(V(t);W(t)\bigr)\le K\,\mathcal E\bigl(V(t)\bigr)\qquad(0\le t<T).
--   $$
--   Then $\mathcal E(V(T))=0$.
--
--   This is the Gronwall step in the uniqueness proof: the difference of two solutions has zero energy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergyCurve.lean#L64-L84

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound
    {V W : ℝ → Lp Space 2 (volume : Measure Space)}
    (hV : ContinuousOn V (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt V (W t) (Ici 0) t)
    (hzero : V 0 = 0) {T K : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T, l2EnergyRate (V t) (W t) ≤ K * l2Energy (V t)) :
    l2Energy (V T) = 0 := by sorry
