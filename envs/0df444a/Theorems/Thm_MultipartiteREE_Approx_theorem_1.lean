-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_theorem_1
-- name    : MultipartiteREE.Approx.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:48.327578+00:00
-- url     : https://prove2.me/theorems/02fad665-d948-4bf1-b495-60d5356c5eeb
-- title:
--   Theorem 1, p. 8 — uniform approximation for the L class
-- statement:
--   Let $\rho$ have the FA-property on each party in a finite set $M$, and let $L$ be the parties on which the local spectral cutoffs act. For nonnegative $C,D$, there are a rank threshold $r_0$ and a real sequence $Y(r)\to0$ such that every $f\in L_n^{|M|}(C,D)$ satisfies
--
--   $$|f(\Lambda_r^L(\rho))-f(\rho)|\le Y(r)\qquad(r\ge r_0).$$
--
--   The same $r_0$ and $Y$ work for every function in the class. This is the $L$-class part of the paper's theorem, with the FA parties relabeled by $M$; the paper also gives assertions for the larger hatted class and the $N$ class.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 8, Theorem 1, L-class assertion

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem theorem_1 {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)]
    (rho : State (Joint I)) (M L : Finset (Fin n))
    (hFA : ∀ s ∈ M, HasFAProperty (marginal rho.coefficients s)) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ r0 : ℕ, ∃ Y : ℕ → ℝ, Tendsto Y atTop (𝓝 0) ∧
      ∀ f : State (Joint I) → ℝ, InClassL M C D f →
        ∀ r ≥ r0, ∀ rhoR : State (Joint I), IsApproxState L r rho rhoR →
          |f rhoR - f rho| ≤ Y r := by sorry

end MultipartiteREE.Approx
