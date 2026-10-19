-- Prove2me | Theorems.Thm_OAI_KervaireBoundary_phase_boundary_cycles
-- name    : OAI.KervaireBoundary.phase_boundary_cycles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:21:14.00556+00:00
-- url     : https://prove2.me/theorems/034f8959-2072-4c11-9c64-0eabb3b3fbed
-- title:
--   Phase of a rotation-weighted shift through face holonomies
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,a_dx)}$. The group phase $\mathrm{gph}_z(a)$ is the phase of $zL(a)$ at $\delta_1$. Let the weights be rotations $u_d=e^{2\pi i\gamma_d}$, and write the cycles of $\sigma$ in coordinates $e(z,i)$ with $n_z+1$ elements. If $\sum_{d\in\text{cycle }z}\gamma_d=\eta_z$ for each cycle $z$, then
--   $$
--   \mathrm{Ph}\bigl(W(\sigma,e^{2\pi i\gamma},a)\bigr)=\frac{|D|-|Z|}2+\sum_z\mathrm{gph}_{e^{2\pi i\eta_z}}\bigl(\text{holonomy of }a\text{ around }z\bigr).
--   $$
--
--   Rotation weights enter only through their sums $\eta_z$ around each cycle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MixingOperators.lean#L350-L371

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

open OAI
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
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

theorem OAI.KervaireBoundary.phase_boundary_cycles (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (σ : Equiv.Perm D) (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (γ : D → ℝ) (a : D → A) (η : Z → ℝ)
    (hη : ∀ z, (∑ d, if (e.symm d).1 = z then γ d else 0) = η z) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ (fun d ↦ scalarRotation (γ d)) a
      (fun d ↦ scalarRotation_unitary (γ d)))
    KervaireMatrix.phase (weightedShift σ (fun d ↦ scalarRotation (γ d)) a) =
      ((Fintype.card D : ℝ) - Fintype.card Z) / 2 +
        ∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _)
          (orbitWeight (finRotate (n z+1)) (fun i ↦ a (e ⟨z,i⟩)) (n z+1) 0) := by sorry
