-- Prove2me | Theorems.Thm_OAI_BeamLadder_adjoint_covariance
-- name    : OAI.BeamLadder.adjoint_covariance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:14:52.503323+00:00
-- url     : https://prove2.me/theorems/26077647-9cb1-488c-93cb-1ab2c4d37bbf
-- title:
--   An intertwining relation by a unitary passes to adjoints
-- statement:
--   Let $E$ be a complex Hilbert space, $U:E\to E$ a unitary (a surjective linear isometry), and $A,B$ bounded linear operators on $E$, with adjoints $A^*$, $B^*$.
--
--   **Theorem.** If $AU=UB$, then
--   $$
--   A^*\,U=U\,B^* .
--   $$
--
--   Equivalently, $U^{-1}AU=B$ implies $U^{-1}A^*U=B^*$: conjugation by a unitary commutes with taking adjoints. It is used to turn covariance relations for weighted lowering operators under the beam splitter into the corresponding relations for their adjoints, the weighted raising operators.
--
--   **Formalization Note** $U$ is a linear isometric equivalence `E ≃ₗᵢ[ℂ] E` coerced to a continuous linear map, and adjoints are `ContinuousLinearMap.adjoint`; completeness of $E$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L286-L304

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace

open OAI OAI.BeamLadder
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.BeamLadder.adjoint_covariance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (A B : E →L[ℂ] E)
    (h : A ∘L U.toContinuousLinearEquiv.toContinuousLinearMap=
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L B) :
    A.adjoint ∘L U.toContinuousLinearEquiv.toContinuousLinearMap=
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L B.adjoint := by sorry
