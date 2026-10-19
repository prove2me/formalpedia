-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_guarded_solid_box_motion
-- name    : OAI.BalancedTransport.Effectivity.elementary_guarded_solid_box_motion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:44:47.369902+00:00
-- url     : https://prove2.me/theorems/708366f5-9e42-422f-9aa9-08c78a60b631
-- title:
--   Elementary volume-preserving motion between two rational box layouts
-- statement:
--   A box layout assigns to each index $i$ of a finite set a centre $c_i\in\mathbb R^3$ and half-widths $w_i\in\mathbb R^3$, describing the box $\prod_k[c_{ik}-w_{ik},c_{ik}+w_{ik}]$. It is $\eta$-separated when distinct boxes satisfy $w_{ik}+w_{jk}+4\eta<|c_{ik}-c_{jk}|$ in some coordinate $k$, and guarded on a set of safe indices when every safe box lies in $\{x_0>2\}$. Let $A$ and $B$ be rational layouts on the same index set with positive half-widths. Assume both are $0$-separated (their closed boxes are pairwise disjoint) and both are guarded on a set of safe indices. Assume also that corresponding boxes have equal volumes:
--   $$
--   \prod_kw^A_{ik}=\prod_kw^B_{ik}\qquad\text{for every }i.
--   $$
--   Then there are a rational $\eta>0$ and an elementary box motion from $A$ to $B$ with margin $\eta$. Throughout the motion the boxes stay $\eta$-separated, keep their volumes, and keep the safe boxes guarded.
--
--   This compiles one step of the recorder, which moves all source boxes onto the corresponding target boxes simultaneously, into an explicit computable motion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryRouting.lean#L109-L209

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

theorem OAI.BalancedTransport.Effectivity.elementary_guarded_solid_box_motion (A B : BoxLayout ι) (safe : Set ι)
    (Ar : RationalLayout A) (Br : RationalLayout B)
    (hA : A.Positive) (hB : B.Positive)
    (hsA : A.Separated 0) (hsB : B.Separated 0)
    (hvol : ∀ i, ∏ k, A.width i k = ∏ k, B.width i k)
    (hgA : A.Guarded safe) (hgB : B.Guarded safe) :
    ∃ η : ℚ, 0 < η ∧ ∃ m : BoxMotion A B safe (η : ℝ), ElementaryMotion m := by sorry
