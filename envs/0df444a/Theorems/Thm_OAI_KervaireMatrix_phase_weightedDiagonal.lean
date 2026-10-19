-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_weightedDiagonal
-- name    : OAI.KervaireMatrix.phase_weightedDiagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:02:29.877765+00:00
-- url     : https://prove2.me/theorems/09e45c28-3ea1-4202-9c35-5ec0eee6898d
-- title:
--   Phase of a diagonal weighted shift
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. Here $\mathrm{ph}_\xi$ integrates the fractional part of $\arg z/2\pi$ against the spectral measure of $\xi$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a:D\to A$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,\,a_dx)}$. For the identity permutation, the weighted shift is the diagonal operator $\delta_{(d,x)}\mapsto u_d\,\delta_{(d,a_dx)}$, and
--   $$
--   \mathrm{Ph}\bigl(W(\mathrm{id},u,a)\bigr)=\sum_{d\in D}\mathrm{gph}_{u_d}(a_d).
--   $$
--   Here $\mathrm{gph}_z(a)$ is the phase of $zL(a)$ at $\delta_1$.
--
--   A block-diagonal unitary has the sum of the phases of its blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean#L197-L215

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

theorem OAI.KervaireMatrix.phase_weightedDiagonal (u : D → ℂ) (a : D → A)
    (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (Equiv.refl D) u a hu)
    phase (weightedShift (Equiv.refl D) u a) = ∑ i, groupPhase (u i) (hu i) (a i) := by sorry
