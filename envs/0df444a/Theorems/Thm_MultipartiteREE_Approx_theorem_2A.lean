-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_theorem_2A
-- name    : MultipartiteREE.Approx.theorem_2A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:35.093501+00:00
-- url     : https://prove2.me/theorems/e7c14ee8-911a-4909-a650-2149a60cb38d
-- title:
--   Theorem 2 A), p. 14 — lower semicontinuity of E_R
-- statement:
--   Let $\rho_0$ be an $n$-partite state with the FA-property on at least $n-1$ marginals. Then $E_R(\rho_0)$ is finite. For every sequence of states $\rho_k$ converging to $\rho_0$ in trace norm, with no FA assumption on its terms,
--
--   $$E_R(\rho_0)\le\liminf_{k\to\infty}E_R(\rho_k).$$
--
--   Thus $E_R$ is lower semicontinuous at every state in $\mathfrak S_*$. This is the $E_R$ case of Theorem 2 A); the regularized $E_R^\infty$ case is not posed here.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 14, Theorem 2 A), E_R case, Eq. (35)

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem theorem_2A {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)]
    (rho0 : State (Joint I)) (h0 : rho0 ∈ SStar I) :
    relEntEnt rho0 < ⊤ ∧
    ∀ rho : ℕ → State (Joint I), Tendsto rho atTop (𝓝 rho0) →
      relEntEnt rho0 ≤ liminf (fun k => relEntEnt (rho k)) atTop := by sorry

end MultipartiteREE.Approx
