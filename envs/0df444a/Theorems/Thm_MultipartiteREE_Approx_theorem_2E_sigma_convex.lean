-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_theorem_2E_sigma_convex
-- name    : MultipartiteREE.Approx.theorem_2E_sigma_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:58.02764+00:00
-- url     : https://prove2.me/theorems/97505774-24fa-443e-aca7-8e62457d5027
-- title:
--   Theorem 2 E), p. 15 — σ-convexity of E_R (first sentence)
-- statement:
--   Let $\{\rho_i\}_{i\ge1}$ be a countable collection of states of the $n$-partite system $A_1\dots A_n$ and $\{p_i\}$ a probability distribution, and let $\rho=\sum_{i=1}^{+\infty}p_i\rho_i$ (the series converges in trace norm). Then the relative entropy of entanglement is $\sigma$-convex:
--
--   $$E_R(\rho)\le\sum_{i=1}^{+\infty}p_iE_R(\rho_i).$$
--
--   Together with Lemma 3 this yields the marginal-entropy upper bound (28) for mixed states.
--
--   **Formalization Note** Collections are indexed by $\mathbb N$; a finite collection is the case of eventually zero weights. The mixture is stated entrywise in the product basis, which is equivalent to trace-norm convergence of the series for a state. Both sides are in $[0,+\infty]$, so the right-hand series always has a value. The $\mu$-integrability sentence and inequality (37) of Theorem 2 E) are not part of this item.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 15, Theorem 2 E), first sentence

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem theorem_2E_sigma_convex {n : ℕ} {I : Fin n → Type} [∀ s, Countable (I s)]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : HasSum p 1) (rho : ℕ → State (Joint I))
    (rhoBar : State (Joint I))
    (hbar : ∀ x y, rhoBar.coefficients x y = ∑' i, (p i : ℂ) * (rho i).coefficients x y) :
    relEntEnt rhoBar ≤ ∑' i, ENNReal.ofReal (p i) * relEntEnt (rho i) := by sorry

end MultipartiteREE.Approx
