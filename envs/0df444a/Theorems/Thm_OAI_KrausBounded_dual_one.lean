-- Prove2me | Theorems.Thm_OAI_KrausBounded_dual_one
-- name    : OAI.KrausBounded.dual_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:42:55.299911+00:00
-- url     : https://prove2.me/theorems/00b2ecaf-1fec-413f-a6d5-e2b0b90bb94a
-- title:
--   The dual map of an isometric operator family is unital
-- statement:
--   Let $E$ and $H$ be complex Hilbert spaces, $I$ an index set, and $(V_i)_{i\in I}$ a family of bounded operators $V_i:E\to H$ such that for every $x\in E$ the series $\sum_i\|V_ix\|^2$ converges to $\|x\|^2$. Let $A:E\to\ell^2(I;H)$, $Ax=(V_ix)_i$, and for a bounded operator $Z$ on $H$ let $A_Z:E\to\ell^2(I;H)$, $A_Zx=(ZV_ix)_i$. The dual (Heisenberg-picture) map is $\Psi(Z)=A^*A_Z$, a bounded operator on $E$ characterized by $\langle x,\Psi(Z)y\rangle=\sum_i\langle V_ix,\,ZV_iy\rangle$. The theorem states that $\Psi$ is unital:
--
--   $$
--   \Psi(1_H)=1_E .
--   $$
--
--   Informally, $\sum_iV_i^*V_i=1_E$: an isometric Kraus family defines a unital completely positive map in the Heisenberg picture. In the photon-number development this is used to show that conditional slices of beam-splitter observables (partial expectations against a normalized vector family) map the identity to the identity.
--
--   **Formalization Note** The dual map is `KrausBounded.dual V hV`, built as the composition of the adjoint of the analysis map with the "acted" analysis map; the hypothesis `hV` is the isometry condition stated as a `HasSum` for every vector.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L549-L561

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator

open OAI OAI.KrausBounded
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KrausBounded.dual_one (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    dual V hV (1 : H →L[ℂ] H)=1 := by sorry
