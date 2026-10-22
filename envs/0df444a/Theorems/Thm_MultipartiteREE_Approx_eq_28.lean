-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_eq_28
-- name    : MultipartiteREE.Approx.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:32.466994+00:00
-- url     : https://prove2.me/theorems/ef2667e7-0308-4241-83f3-90399e59bb33
-- title:
--   Eq. (28), p. 11 — bound by any n−1 marginal entropies
-- statement:
--   For an $n$-partite state $\rho$, any one party $t$ may be omitted from the entropy sum:
--
--   $$E_R(\rho)\le\sum_{s\ne t}H(\rho_{A_s}).$$
--
--   The paper states (28) for the first $n-1$ parties and immediately says the same bound holds for any choice of $n-1$ parties. Entropies and $E_R$ are extended nonnegative reals, so an infinite right side is allowed.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 11, Eq. (28) and paragraph after it

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem eq_28 {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)]
    (rho : State (Joint I)) (t : Fin n) :
    relEntEnt rho ≤ ∑ s ∈ Finset.univ.erase t, marginalEntropy rho s := by sorry

end MultipartiteREE.Approx
