-- Prove2me | Theorems.Thm_MultibrotCorr_theorem_2_2
-- name    : MultibrotCorr.theorem_2_2
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:33:28.70818+00:00
-- url     : https://prove2.me/theorems/f0e5fd42-cb67-4df5-82f3-11bf212f51fd
-- title:
--   Theorem 2.2 — similarity transfer under a univalent map
-- statement:
--   Let $A_1,A_2,B$ be nonempty closed subsets of $\mathbb{C}$, and suppose $A_1$ is asymptotically $\lambda$-self-similar about $c\in A_1$ with limit model $B$. If $f$ is a univalent map sending a relatively open subset of $A_1$ containing $c$ onto a relatively open subset of $A_2$ containing $f(c)$, then $A_2$ is asymptotically self-similar about $f(c)$ with the same scale $\lambda$ and limit model $f'(c)\cdot B$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Theorem 2.2, Section 2.2; citing Tan Lei (1990), Proposition 2.4, p. 593.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem theorem_2_2 (A1 A2 B : Set ℂ) (c lam : ℂ) (f : ℂ → ℂ)
    (hA1 : IsClosed A1 ∧ A1.Nonempty) (hA2 : IsClosed A2 ∧ A2.Nonempty)
    (hB : IsClosed B ∧ B.Nonempty)
    (hsim : IsAsymptoticallySelfSimilar A1 c lam B)
    (O1 O2 : Set ℂ) (hO1 : IsOpen O1) (hO2 : IsOpen O2) (hc : c ∈ O1)
    (hf : DifferentiableOn ℂ f O1 ∧ Set.InjOn f O1)
    (hmap : f '' (A1 ∩ O1) = A2 ∩ O2) (hfc : f c ∈ O2) :
    IsAsymptoticallySelfSimilar A2 (f c) lam ((fun z => deriv f c * z) '' B) := by sorry
end MultibrotCorr
