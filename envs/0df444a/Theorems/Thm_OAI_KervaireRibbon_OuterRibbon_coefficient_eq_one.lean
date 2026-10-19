-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_OuterRibbon_coefficient_eq_one
-- name    : OAI.KervaireRibbon.OuterRibbon.coefficient_eq_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:08:07.277503+00:00
-- url     : https://prove2.me/theorems/5b45b27d-8812-425e-aa64-5921b406cc79
-- title:
--   Ribbon values in the base group are trivial
-- statement:
--   Let $A$ be a group, $I$ a nonempty finite set with a cyclic permutation $\rho$, $a:I\to A$ the relator coefficients, and $s:I\to\{1,-1\}$ the exponents with $\sum_is_i=\pm1$. An outer ribbon with marker $o$ and boundary list $l$ consists of a planar pair $(\sigma,\theta)$ with $\theta$ an involution, signs $t$ with $t(\theta d)=-t(d)$, a disk atlas disjoint from the boundary, and potentials $u$ satisfying every relator corner. The marker is fixed by $\theta$ with sign $0$, the list $o::l$ is a repetition-free circle of $\sigma$, darts of $l$ have signs $\pm1$, and every other dart is a disk dart or fixed by both permutations. Its value is the boundary word $\prod_{d\in o::l}t^{t(d)}\,u(\theta d)u(\sigma d)^{-1}$ in the free product $A*\langle t\rangle$. If an outer ribbon $r$ has value in $A$, that is $\mathrm{value}(r)=g\in A\subseteq A*\langle t\rangle$, then
--   $$
--   g=1 .
--   $$
--
--   This is the combinatorial core of the proof: an element of the normal closure of the relator that is represented by a ribbon diagram and lies in $A$ is trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/OuterRibbon.lean#L259-L290

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
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

theorem OAI.KervaireRibbon.OuterRibbon.coefficient_eq_one [Nonempty I]
    {ρ : Perm I} (hρ : ∀ i j, ρ.SameCycle i j) {a : I → A}
    {s : I → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    {o : D} {l : List D} (r : OuterRibbon (V := V) ρ a s o l) (g : A)
    (he : r.value = Coprod.inl g) : g = 1 := by sorry
