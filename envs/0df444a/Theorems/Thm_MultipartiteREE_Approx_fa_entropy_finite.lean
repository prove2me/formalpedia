-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_fa_entropy_finite
-- name    : MultipartiteREE.Approx.fa_entropy_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:34.861769+00:00
-- url     : https://prove2.me/theorems/97dbb425-f570-4d24-9b1f-24059d539ba4
-- title:
--   p. 4 — FA-property implies finite entropy
-- statement:
--   A state with the FA-property has finite von Neumann entropy. If $\omega$ is a state and its eigenvalues admit the nonnegative sequence required by (1), then
--
--   $$H(\omega)<+\infty.$$
--
--   This is the entropy fact used to turn the marginal bound (28) into finiteness of $E_R$ on $\mathfrak S_*$.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 4, statement after (3)

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem fa_entropy_finite {J : Type} [Countable J] (omega : State J)
    (h : HasFAProperty omega.coefficients) : homogeneousEntropy omega.coefficients < ⊤ := by sorry

end MultipartiteREE.Approx
