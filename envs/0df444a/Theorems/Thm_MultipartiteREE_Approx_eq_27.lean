-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_eq_27
-- name    : MultipartiteREE.Approx.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:41.078596+00:00
-- url     : https://prove2.me/theorems/99aea5a3-f8d7-4d88-be7c-ed00f7ea6fbc
-- title:
--   Eq. (27), p. 11 — concavity defect of E_R is at most h₂(p)
-- statement:
--   Let $\rho$ and $\sigma$ be states of the $n$-partite system $A_1\dots A_n$ with finite relative entropy of entanglement, and let $p\in[0,1]$. Write $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ for the binary entropy (natural logarithm, $0\ln0=0$). Then
--
--   $$pE_R(\rho)+(1-p)E_R(\sigma)\le E_R(p\rho+(1-p)\sigma)+h_2(p).$$
--
--   Combined with the convexity of $E_R$, this gives the almost-affinity estimate (14) required for membership of $E_R$ in the class $L^{n-1}_n(1,1)$.
--
--   **Formalization Note** The paper states that (27) remains valid in infinite dimension "provided that all the involved quantities are finite" (p. 11); this proviso is the pair of hypotheses $E_R(\rho),E_R(\sigma)<+\infty$ (finiteness of $E_R$ of the mixture then follows by convexity). Under these hypotheses all three values are converted to real numbers. At $p\in\{0,1\}$ the Lean `Real.log` convention gives $h_2(p)=0$, matching $0\ln 0=0$.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 11, Eq. (27) and §4.1 (validity in infinite dimension)

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem eq_27 {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)]
    (rho sigma tau : State (Joint I)) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hmix : IsMixture p rho sigma tau) (hr : relEntEnt rho ≠ ⊤) (hs : relEntEnt sigma ≠ ⊤) :
    p * (relEntEnt rho).toReal + (1 - p) * (relEntEnt sigma).toReal ≤
      (relEntEnt tau).toReal + binEnt p := by sorry

end MultipartiteREE.Approx
