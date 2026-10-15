-- Prove2me | Theorems.Thm_OAI_QAC_three_factor_transition
-- name    : OAI.QAC.three_factor_transition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:37:11.279966+00:00
-- url     : https://prove2.me/theorems/695f2464-4613-4387-a342-f7d0679bffde
-- title:
--   Telescoping bound for a transition through three contractions
-- statement:
--   Let $\mathcal A$ be a unital $C^{*}$-algebra, let $H,P,H_1,H_2,B_1,B_2,B_3\in\mathcal A$ and $\delta\in\mathbb R$. Assume the norm bounds
--   $$\|H\|\le1,\qquad\|P\|\le1,\qquad\|1-H_1\|\le1,\qquad\|B_1\|\le1,\quad\|B_2\|\le1,\quad\|B_3\|\le1,$$
--   and the three one-step transition bounds
--   $$
--   \|H_1B_3P\|\le\delta,\qquad\|H_2B_2(1-H_1)\|\le\delta,\qquad\|HB_1(1-H_2)\|\le\delta .
--   $$
--   Then
--   $$
--   \|HB_1B_2B_3P\|\le3\delta .
--   $$
--
--   Think of $P$ as an initial subspace, of $H_1,H_2,H$ as projections onto states above successively higher thresholds, and of $B_3,B_2,B_1$ as three successive operations: if each operation moves states from below one threshold to above the next one only with amplitude $\delta$, then the three operations together move states from $P$ to $H$ with amplitude at most $3\delta$. In the localization argument it bounds a product of three evolved product projections, arising from the expansion of a reflection layer, between a zero-mismatch projection and a high mismatch projection.
--
--   **Formalization Note** No norm bound on $H_2$ is required. The statement is made in any type with a `CStarAlgebra` instance, although the argument only uses the normed-ring structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean#L153-L172

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

theorem OAI.QAC.three_factor_transition (H P H₁ H₂ B₁ B₂ B₃ : A) {δ : ℝ}
    (hH : ‖H‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hE₁ : ‖1-H₁‖ ≤ 1)
    (hB₁ : ‖B₁‖ ≤ 1) (hB₂ : ‖B₂‖ ≤ 1) (hB₃ : ‖B₃‖ ≤ 1)
    (h₁ : ‖H₁*B₃*P‖ ≤ δ) (h₂ : ‖H₂*B₂*(1-H₁)‖ ≤ δ)
    (h₃ : ‖H*B₁*(1-H₂)‖ ≤ δ) : ‖H*B₁*B₂*B₃*P‖ ≤ 3*δ := by sorry
