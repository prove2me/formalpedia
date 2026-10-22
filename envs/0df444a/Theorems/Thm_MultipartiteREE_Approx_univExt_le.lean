-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_univExt_le
-- name    : MultipartiteREE.Approx.univExt_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:48.287366+00:00
-- url     : https://prove2.me/theorems/ad092dfa-4cd8-4cff-9f7f-4f474007094b
-- title:
--   p. 14 — universal extension lies below E_R
-- statement:
--   For every multipartite state $\rho$, the universal extension of the relative entropy of entanglement does not exceed the direct relative entropy of entanglement:
--
--   $$\widehat E_R(\rho)\le E_R(\rho).$$
--
--   This compares the lower semicontinuous extension obtained from local finite-rank compressions with the direct infimum over separable states. The paper gives a parallel inequality for the regularized measure.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 14, display after (33), first inequality

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem univExt_le {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)] (rho : State (Joint I)) :
    univExt rho ≤ relEntEnt rho := by sorry

end MultipartiteREE.Approx
