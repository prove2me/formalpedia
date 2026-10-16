-- Prove2me | Theorems.Thm_OAI_QuantumTrace_sliceMoment_bounded_representation
-- name    : OAI.QuantumTrace.sliceMoment_bounded_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:59:23.051973+00:00
-- url     : https://prove2.me/theorems/742a88fa-5a2e-450e-a6a0-a7553a1149a1
-- title:
--   Bounded sliced weighted moments are quadratic forms of positive operators
-- statement:
--   Let $E$ be a complex Hilbert space with a Hilbert (orthonormal) basis $(b_j)_{j\in J}$, let $w:J\to\mathbb R$ with $w_j\ge0$, let $(V_i)_{i\in I}$ be a family of bounded operators on $E$ and $S$ a bounded operator on $E$. For $y\in E$ define the sliced moment
--   $$\Theta(y)=\sum_{i\in I}\sum_{j\in J}w_j\,|\langle b_j,V_iy\rangle|^2\in[0,\infty].$$
--   Assume there is $C\ge0$ with $\Theta(Sx)\le C\|x\|^2$ for all $x\in E$. Then there is a positive bounded operator $B$ on $E$ with
--
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=\Theta(Sx)\qquad\text{for every }x\in E .
--   $$
--
--   Thus a nonnegative quadratic form of "sum of squares" type that is bounded by $C\|x\|^2$ is represented by a bounded positive operator. With $w_j=-\log p_j$ for the eigenvalues of a state and $(V_i)$ a Kraus family, $\Theta$ is the form of $\sum_iV_i^*(-\log\rho)V_i$, and the theorem turns a form bound into an actual operator.
--
--   **Formalization Note** $\Theta$ is `sliceMoment b (fun j => ENNReal.ofReal (w j)) V`, an `ENNReal` double series, and the conclusion is stated as `ENNReal.ofReal (Re ⟨x, B x⟩) = sliceMoment ...`; since $B$ is positive the real part is nonnegative, so this is an equality of nonnegative reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1698-L1718

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy

open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

theorem OAI.QuantumTrace.sliceMoment_bounded_representation (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) ≤
      ENNReal.ofReal (C*‖x‖^2)) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) := by sorry
