-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_dart_pinch
-- name    : OAI.KervaireRibbon.dart_pinch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:01:55.211863+00:00
-- url     : https://prove2.me/theorems/4fed57ce-9001-4054-825b-b508f3ac27a2
-- title:
--   A boundary word in the base group has a pinch
-- statement:
--   Let $A$ be a group and $A*\langle t\rangle$ its free product with an infinite cyclic group. Let $l$ be a nonempty list of darts with signs $t_d\in\{1,-1\}$ and coefficients $c_d\in A$. If $\prod_{d\in l}t^{t_d}c_d$ lies in $A$, then $l$ has consecutive entries $x,y$ with
--   $$
--   c_x=1\qquad\text{and}\qquad t_y=-t_x .
--   $$
--
--   So the word contains a pinch $t^{\pm1}\cdot1\cdot t^{\mp1}$; this is Britton's lemma for $A*\langle t\rangle$ as an HNN extension of $A$ with trivial associated subgroups.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Circles.lean#L115-L155

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles

open OAI OAI.KervaireRibbon
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]

theorem OAI.KervaireRibbon.dart_pinch (t : D → ℤ) (c : D → A) (l : List D) (hl : l ≠ [])
    (ht : ∀ d ∈ l, t d = 1 ∨ t d = -1) (g : A)
    (he : dartEval t c l = Coprod.inl g) :
    ∃ pre post x y, l = pre ++ x::y::post ∧ c x = 1 ∧ t y = -t x := by sorry
