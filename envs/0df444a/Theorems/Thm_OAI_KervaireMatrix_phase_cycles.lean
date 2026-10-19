-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_cycles
-- name    : OAI.KervaireMatrix.phase_cycles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:18:46.935719+00:00
-- url     : https://prove2.me/theorems/f505b2ad-abd6-415c-a3bb-2f3079d915c6
-- title:
--   Phase of a weighted shift through its cycles
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,a_dx)}$. The group phase $\mathrm{gph}_z(a)$ is the phase of $zL(a)$ at $\delta_1$. Write the cycles of $\sigma$ in coordinates $e(z,i)$ with $\sigma(e(z,i))=e(z,i+1\bmod n_z+1)$. Then
--   $$
--   \mathrm{Ph}\bigl(W(\sigma,u,a)\bigr)=\sum_z\Bigl(\frac{n_z}2+\mathrm{gph}_{\prod_iu_{e(z,i)}}\Bigl(\prod_ia_{e(z,i)}\Bigr)\Bigr),
--   $$
--   with the products taken in cycle order.
--
--   The phase of a weighted shift is thus read off from the holonomies of its cycles.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MixingOperators.lean#L204-L230

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

open OAI OAI.KervaireMatrix
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
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]

theorem OAI.KervaireMatrix.phase_cycles {Z : Type*} [Fintype Z] (n : Z → ℕ)
    (e : (Σ z, Fin (n z+1)) ≃ D) (σ : Equiv.Perm D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (u : D → ℂ) (a : D → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
    KervaireMatrix.phase (weightedShift σ u a) =
      ∑ z, ((n z : ℝ)/2 + groupPhase
        (orbitWeight (finRotate (n z+1)) (fun i ↦ u (e ⟨z,i⟩)) (n z+1) 0)
        (orbitWeight_mem (unitary ℂ) _ _ (fun i ↦ hu (e ⟨z,i⟩)) _ _)
        (orbitWeight (finRotate (n z+1)) (fun i ↦ a (e ⟨z,i⟩)) (n z+1) 0)) := by sorry
