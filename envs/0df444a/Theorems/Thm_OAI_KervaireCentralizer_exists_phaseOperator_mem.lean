-- Prove2me | Theorems.Thm_OAI_KervaireCentralizer_exists_phaseOperator_mem
-- name    : OAI.KervaireCentralizer.exists_phaseOperator_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:50:23.597228+00:00
-- url     : https://prove2.me/theorems/350f17e6-b90f-4ec4-afe5-17dc27a219cb
-- title:
--   Phase operators stay in centralizer algebras
-- statement:
--   Let $S$ be a set of operators on a Hilbert space and $\mathcal A$ the algebra of operators commuting with $S$. For every unitary $U$ in $\mathcal A$ there is $B\in\mathcal A$ with
--   $$
--   B\ge0,\qquad e^{2\pi iB}=U,\qquad\mathrm{Re}\langle\xi,B\xi\rangle=\mathrm{ph}_\xi(U)\ \text{ for all }\xi .
--   $$
--
--   Here $\mathrm{ph}_\xi(U)$ is the fractional phase of $U$ at $\xi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseSubadditivity.lean#L160-L184

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

theorem OAI.KervaireCentralizer.exists_phaseOperator_mem (S : Set (Operator (H := H))) (U : algebra S)
    (hU : U ∈ unitary (algebra S)) :
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S U).mp hU)
    ∃ B : algebra S, 0 ≤ B ∧ NormedSpace.exp (phaseVelocity B) = U ∧
      ∀ ξ : H, (vectorCLM ξ (B : Operator (H := H))).re = vectorPhase (U : Operator (H := H)) ξ := by sorry
