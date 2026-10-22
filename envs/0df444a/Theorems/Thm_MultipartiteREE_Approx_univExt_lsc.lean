-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_univExt_lsc
-- name    : MultipartiteREE.Approx.univExt_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:56.136029+00:00
-- url     : https://prove2.me/theorems/e76f6b6c-05af-4dd9-a63e-374edbaea77f
-- title:
--   p. 13 — universal extension of E_R is lower semicontinuous
-- statement:
--   The universal extension of relative entropy of entanglement is lower semicontinuous on the full state space:
--
--   $$\widehat E_R:\mathfrak S(\mathcal H_{A_1\cdots A_n})\longrightarrow[0,+\infty]\quad\text{is lower semicontinuous}.$$
--
--   The paper obtains this as the first part of the first bullet after applying Proposition 1 to $E_R$. Its entanglement-monotone clause is outside this milestone.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 13, first bullet after Proposition 1

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem univExt_lsc {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)] :
    LowerSemicontinuous (univExt (I := I)) := by sorry

end MultipartiteREE.Approx
