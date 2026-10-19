-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_evacuateToParking
-- name    : OAI.BalancedTransport.Effectivity.elementary_evacuateToParking
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:43:21.336108+00:00
-- url     : https://prove2.me/theorems/c38d85ef-8085-4912-b135-74ae8ed7e7fd
-- title:
--   Moving all boxes to parking positions by an elementary motion
-- statement:
--   Let $a_i$ be current centres, $p_i$ parking centres and $w_i$ positive half-widths, all rational, with $w_{ik}+w_{jk}+4\eta\le D$ for all $i,j,k$ and $D\ge0$. Assume:
--
--   - the centres $a_i$ are $D$-separated (distinct centres differ by more than $D$ in some coordinate);
--   - $|a_{i0}-p_{j0}|>D$ for all $i,j$, and $|p_{i0}-p_{j0}|>D$ for $i\ne j$;
--   - $H$ is a rational height with $H-a_{i1}>D$ and $H-p_{i1}>D$ for all $i$;
--   - both layouts keep the safe boxes in $\{x_0>2\}$.
--
--   A box motion is elementary when all its centre and width coordinates are elementary functions of time.
--
--   Then there is an elementary box motion
--   $$
--   (a,w)\ \longrightarrow\ (p,w)
--   $$
--   that keeps the half-widths, stays $\eta$-separated and keeps the safe boxes guarded throughout.
--
--   Routing the recorder's source boxes to their target boxes goes through such parking layouts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryParking.lean#L95-L128

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.BalancedTransport.Effectivity.elementary_evacuateToParking {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (pr : RationalCenters p) (wr : RationalCenters w)
    (Hr : RationalConstant H)
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe) :
    ∃ m : BoxMotion ⟨a, w⟩ ⟨p, w⟩ safe η, ElementaryMotion m := by sorry
