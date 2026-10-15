-- Prove2me | Theorems.Thm_OAI_QAC_projection_transition_square
-- name    : OAI.QAC.projection_transition_square
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:33:51.882977+00:00
-- url     : https://prove2.me/theorems/2d0741f0-fc52-4318-bca1-1825e2536e5d
-- title:
--   Squared transition bound for projections through an approximating element
-- statement:
--   Let $\mathcal A$ be a unital $C^{*}$-algebra, let $H,P,Q\in\mathcal A$ be orthogonal projections (self-adjoint idempotents: $H^{*}=H=H^2$, and likewise for $P$ and $Q$), and let $X\in\mathcal A$ be arbitrary. Then
--   $$
--   \|HQP\|^2\le \|HXP\|+\|(Q-X)\,P\,Q\| .
--   $$
--
--   The element $X$ plays the role of an approximation of the projection $Q$: if the transition $HXP$ of $X$ is small and $X$ is close to $Q$ on the relevant part, then the transition $HQP$ of $Q$ itself is small, at the cost of a square. In the localization argument for constant-depth circuits it is applied with $H$ a high mismatch projection, $P$ a zero-mismatch product projection, $Q=UP_D^0U^{*}$ an evolved product projection and $X=U\,p(\mathcal N_D)\,U^{*}$ an evolved polynomial in a mismatch operator.
--
--   **Formalization Note** The algebra is any type with a `CStarAlgebra` instance (a complete unital normed $*$-algebra over $\mathbb C$ with $\|x^{*}x\|=\|x\|^2$); the projection hypotheses are `IsStarProjection`. No hypothesis is placed on $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean#L28-L47

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix
variable {A : Type*} [CStarAlgebra A]

theorem OAI.QAC.projection_transition_square (H P Q X : A)
    (hH : IsStarProjection H) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖H * Q * P‖^2 ≤ ‖H * X * P‖ + ‖(Q-X) * P * Q‖ := by sorry
