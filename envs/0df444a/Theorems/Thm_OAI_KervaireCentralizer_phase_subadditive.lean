-- Prove2me | Theorems.Thm_OAI_KervaireCentralizer_phase_subadditive
-- name    : OAI.KervaireCentralizer.phase_subadditive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:53:14.056977+00:00
-- url     : https://prove2.me/theorems/e62b0340-d8de-4d63-88b3-d663ecfdc21d
-- title:
--   Subadditivity of traced fractional phases
-- statement:
--   Let $S$ be a set of operators on a nonzero Hilbert space, $\mathcal A$ its centralizer algebra, and $\xi_1,\dots,\xi_m$ vectors such that $\mathrm{Tr}(X)=\sum_j\langle\xi_j,X\xi_j\rangle$ is tracial on $\mathcal A$. With $\mathrm{Ph}(U)=\sum_j\mathrm{ph}_{\xi_j}(U)$, for unitaries $U,V\in\mathcal A$,
--   $$
--   \mathrm{Ph}(UV)\le\mathrm{Ph}(U)+\mathrm{Ph}(V).
--   $$
--
--   For matrices this is the classical subadditivity of the sum of fractional eigenvalue arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseSubadditivity.lean#L186-L213

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

open OAI OAI.KervaireCentralizer
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

theorem OAI.KervaireCentralizer.phase_subadditive [Nontrivial H] (S : Set (Operator (H := H))) (ξ : ι → H)
    (ht : ∀ X Y : algebra S, trace S ξ (X * Y) = trace S ξ (Y * X))
    (U V : algebra S) (hU : U ∈ unitary (algebra S)) (hV : V ∈ unitary (algebra S)) :
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S U).mp hU)
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S V).mp hV)
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S (U*V)).mp ((unitary _).mul_mem hU hV))
    sumPhase ((U*V : algebra S) : Operator (H := H)) ξ ≤
      sumPhase (U : Operator (H := H)) ξ + sumPhase (V : Operator (H := H)) ξ := by sorry
