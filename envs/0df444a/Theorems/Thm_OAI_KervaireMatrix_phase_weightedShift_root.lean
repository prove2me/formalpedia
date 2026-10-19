-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_weightedShift_root
-- name    : OAI.KervaireMatrix.phase_weightedShift_root
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:00:36.900999+00:00
-- url     : https://prove2.me/theorems/d15a3104-a286-414c-8b0b-a3185e13a06b
-- title:
--   Cyclic weighted shifts are invariant under root-of-unity rotations
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. Here $\mathrm{ph}_\xi$ integrates the fractional part of $\arg z/2\pi$ against the spectral measure of $\xi$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a:D\to A$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,\,a_dx)}$. Let $W=W(\mathrm{rot},u,a)$ be the weighted shift of the cyclic rotation of $\{0,\dots,n\}$, and let $z^{n+1}=1$ with $|z|=1$. Then
--   $$
--   \mathrm{Ph}(zW)=\mathrm{Ph}(W).
--   $$
--
--   Rotating a cyclic shift by an $(n+1)$-th root of unity is a unitary conjugation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean#L46-L70

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
variable {A : Type*} [Group A]

theorem OAI.KervaireMatrix.phase_weightedShift_root (n : ℕ) (z : ℂ) (hz : z^(n+1) = 1)
    (hzu : z ∈ unitary ℂ) (u : Fin (n+1) → ℂ) (a : Fin (n+1) → A)
    (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    let _ := isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨z,hzu⟩ (weightedShift_unitary (finRotate (n+1)) u a hu))
    KervaireMatrix.phase (z • weightedShift (finRotate (n+1)) u a) =
      KervaireMatrix.phase (weightedShift (finRotate (n+1)) u a) := by sorry
