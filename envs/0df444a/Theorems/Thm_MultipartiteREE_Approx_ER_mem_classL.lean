-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_ER_mem_classL
-- name    : MultipartiteREE.Approx.ER_mem_classL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:40.492297+00:00
-- url     : https://prove2.me/theorems/6f9577b4-bc36-466c-b3d8-4b89565e78e8
-- title:
--   §4.1, p. 11 — E_R belongs to L_n^{n−1}(1,1)
-- statement:
--   Fix one omitted party $t$. On states with finite entropies for the remaining $n-1$ parties, the relative entropy of entanglement belongs to the approximation class $L_n^{n-1}(1,1)$:
--
--   $$E_R\in L_n^{n-1}(1,1).$$
--
--   This class combines the almost-affinity estimate (14) with the entropy bound (15). It is the class membership invoked when Theorem 1 is applied to $E_R$.
--
--   **Formalization Note** The finite-entropy parties are represented by the complement of $t$, a relabeling of the first $n-1$ parties in the paper. The class is real valued on that domain.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 11, last paragraph of §4.1

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem ER_mem_classL {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)] (t : Fin n) :
    InClassL (Finset.univ.erase t) 1 1 (fun rho : State (Joint I) => (relEntEnt rho).toReal) := by sorry

end MultipartiteREE.Approx
