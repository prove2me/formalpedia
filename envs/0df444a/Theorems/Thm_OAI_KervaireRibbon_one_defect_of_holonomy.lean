-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_one_defect_of_holonomy
-- name    : OAI.KervaireRibbon.one_defect_of_holonomy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:53:24.568932+00:00
-- url     : https://prove2.me/theorems/eb8c5a4b-7b51-4155-a558-ad3647065c63
-- title:
--   Trivial holonomy rules out a single coboundary defect
-- statement:
--   Let $A$ be a group, $\sigma$ a permutation of a finite set $D$ whose cycles are indexed by $Z$ with coordinates $\sigma(e(z,i))=e(z,i+1)$ for $i\in\mathbb Z/(n_z+1)$, and $b,u:D\to A$. Suppose $b(d)=u(\sigma d)\,u(d)^{-1}$ for every $d\ne p$, and that the holonomy of $b$ around every cycle is trivial, $b(e(z,n_z))\cdots b(e(z,0))=1$. Then also
--   $$
--   b(p)=u(\sigma p)\,u(p)^{-1}.
--   $$
--
--   A coboundary condition failing at only one point is restored by trivial holonomy around the cycle through that point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RibbonRigidity.lean#L95-L113

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

open OAI OAI.KervaireRibbon
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open Equiv Equiv.Perm KervaireCycle
open scoped Classical
variable {D A : Type*} [Group A]

theorem OAI.KervaireRibbon.one_defect_of_holonomy [Fintype D] (σ : Equiv.Perm D) (b u : D → A) (p : D)
    {Z : Type*} (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hu : ∀ d, d ≠ p → b d = u (σ d) * (u d)⁻¹)
    (hm : ∀ z, orbitWeight (finRotate (n z+1)) (fun i ↦ b (e ⟨z,i⟩)) (n z+1) 0 = 1) :
    b p = u (σ p) * (u p)⁻¹ := by sorry
