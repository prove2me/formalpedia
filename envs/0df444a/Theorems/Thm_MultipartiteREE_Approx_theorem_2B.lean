-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_theorem_2B
-- name    : MultipartiteREE.Approx.theorem_2B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:59.646845+00:00
-- url     : https://prove2.me/theorems/a006d35e-f13a-4f62-a237-aeb7b5f25114
-- title:
--   Theorem 2 B), p. 14 — E_R equals its universal extension on S_*
-- statement:
--   On states whose marginals have the FA-property for at least $n-1$ parties, direct and universally extended relative entropy of entanglement agree:
--
--   $$E_R(\rho)=\widehat E_R(\rho)\qquad(\rho\in\mathfrak S_*).$$
--
--   This is the $E_R$ part of the first sentence of Theorem 2 B). The regularized equality and the convex-closure assertion are separate claims in the source.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 14, Theorem 2 B), first sentence, E_R case

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem theorem_2B {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)]
    (rho : State (Joint I)) (h : rho ∈ SStar I) : relEntEnt rho = univExt rho := by sorry

end MultipartiteREE.Approx
