-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_grid
-- name    : OAI.KervaireMatrix.phase_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:59:41.716986+00:00
-- url     : https://prove2.me/theorems/5c762994-583e-4c31-8605-e68fcbf79266
-- title:
--   Matrix phases of grid rotations
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. Here $\mathrm{ph}_\xi$ integrates the fractional part of $\arg z/2\pi$ against the spectral measure of $\xi$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a:D\to A$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,\,a_dx)}$. For every unitary $U$ on $\ell^2(D\times A)$ and $d\ge1$,
--   $$
--   \sum_{j=0}^{d-1}\mathrm{Ph}\bigl(e^{2\pi ij/d}U\bigr)=|D|\,\frac{d-1}2+\mathrm{Ph}(U^d).
--   $$
--
--   This is the matrix form of the grid identity for phases.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean#L342-L363

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
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

theorem OAI.KervaireMatrix.phase_grid (U : Operator D A) (hU : U ∈ unitary (Operator D A))
    (d : ℕ) (hd : 0 < d) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
    let _ := fun j : Fin d => isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨scalarRotation ((j.val : ℝ)/d), scalarRotation_unitary _⟩ hU)
    (∑ j : Fin d, KervaireMatrix.phase (scalarRotation ((j.val : ℝ)/d) • U)) =
      (Fintype.card D : ℝ) * ((d : ℝ)-1)/2 + KervaireMatrix.phase (U^d) := by sorry
