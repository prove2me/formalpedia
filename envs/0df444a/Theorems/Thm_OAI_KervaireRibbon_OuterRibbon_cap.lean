-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_OuterRibbon_cap
-- name    : OAI.KervaireRibbon.OuterRibbon.cap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:07:21.409353+00:00
-- url     : https://prove2.me/theorems/3486670f-2374-4df0-904e-7338ce14e111
-- title:
--   Capping a pinch in an outer ribbon
-- statement:
--   Let $A$ be a group, $I$ a nonempty finite set with a cyclic permutation $\rho$, $a:I\to A$ the relator coefficients, and $s:I\to\{1,-1\}$ the exponents with $\sum_is_i=\pm1$. An outer ribbon with marker $o$ and boundary list $l$ consists of a planar pair $(\sigma,\theta)$ with $\theta$ an involution, signs $t$ with $t(\theta d)=-t(d)$, a disk atlas disjoint from the boundary, and potentials $u$ satisfying every relator corner. The marker is fixed by $\theta$ with sign $0$, the list $o::l$ is a repetition-free circle of $\sigma$, darts of $l$ have signs $\pm1$, and every other dart is a disk dart or fixed by both permutations. Its value is the boundary word $\prod_{d\in o::l}t^{t(d)}\,u(\theta d)u(\sigma d)^{-1}$ in the free product $A*\langle t\rangle$. Let $r$ be an outer ribbon with boundary list $\mathrm{pre}\,{+\!\!+}\,x::y::\mathrm{post}$, trivial corner at $x$ and $t(y)=-t(x)$. Then there is an outer ribbon $r'$ with boundary list $\mathrm{pre}\,{+\!\!+}\,\mathrm{post}$ and
--   $$
--   \mathrm{value}(r')=\mathrm{value}(r).
--   $$
--
--   So a pinch $t^{\pm1}\cdot1\cdot t^{\mp1}$ in the boundary word can be capped off inside the class of ribbon diagrams.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/OuterRibbon.lean#L116-L253

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
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

theorem OAI.KervaireRibbon.OuterRibbon.cap [Nonempty I]
    {ρ : Perm I} (hρ : ∀ i j, ρ.SameCycle i j) {a : I → A}
    {s : I → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    {o : D} (pre post : List D) (x y : D)
    (r : OuterRibbon (V := V) ρ a s o (pre++x::y::post))
    (hcx : corner r.σ r.θ r.u x = 1) (hpair : r.t y = -r.t x) :
    ∃ r' : OuterRibbon (V := V) ρ a s o (pre++post), r'.value = r.value := by sorry
