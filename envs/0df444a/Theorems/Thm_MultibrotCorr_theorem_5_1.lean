-- Prove2me | Theorems.Thm_MultibrotCorr_theorem_5_1
-- name    : MultibrotCorr.theorem_5_1
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:35:44.502872+00:00
-- url     : https://prove2.me/theorems/c0d63a01-e857-4b9c-a988-45b4811de8d9
-- title:
--   Theorem 5.1 (Tan Lei) — parameter/dynamical similarity transfer
-- statement:
--   Tan Lei's transfer theorem, as stated (simplified) in the paper. Let $u,\lambda$ be holomorphic on a neighborhood $U$ of $a$ with $u'(a)\ne0$, $u(a)=0$, $|\lambda(a)|>1$. Let $X$ be a closed subset of $U\times\mathbb{C}$ such that (i) for every $c$ near $a$, $0\in X(c)$ and $X(c)$ is $\lambda(c)$-self-similar about $0$ with a common radius $r$; and (ii) there is a dense subset $X'(a)\subset X(a)$ each of whose points extends to a holomorphic section $\zeta_x(c)\in X(c)$ near $a$. Then $M_u=\{c\in U:u(c)\in X(c)\}$ is asymptotically $\lambda(a)$-self-similar about $a$ with limit model $u'(a)^{-1}\cdot X(a)$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Theorem 5.1, Section 5; citing Tan Lei, Similarity between the Mandelbrot set and Julia sets, Comm. Math. Phys. 134 (1990), Proposition 4.1, p. 601.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem theorem_5_1 (U : Set ℂ) (a : ℂ) (u lam : ℂ → ℂ) (X : Set (ℂ × ℂ))
    (hU : IsOpen U) (haU : a ∈ U)
    (hu : DifferentiableOn ℂ u U) (hlam : DifferentiableOn ℂ lam U)
    (hu' : deriv u a ≠ 0) (hu0 : u a = 0) (hlam1 : 1 < ‖lam a‖)
    (hX : ∃ C : Set (ℂ × ℂ), IsClosed C ∧ X = C ∩ (U ×ˢ Set.univ))
    (hself : ∃ (r : ℝ) (V : Set ℂ), 0 < r ∧ IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∀ c ∈ V, (0 : ℂ) ∈ Xfiber X c ∧
        truncSet ((fun z => lam c * z) '' Xfiber X c) r = truncSet (Xfiber X c) r)
    (hdense : ∃ X' : Set ℂ, X' ⊆ Xfiber X a ∧ Xfiber X a ⊆ closure X' ∧
      ∀ x ∈ X', ∃ (Vx : Set ℂ) (ζ : ℂ → ℂ), IsOpen Vx ∧ a ∈ Vx ∧ Vx ⊆ U ∧
        DifferentiableOn ℂ ζ Vx ∧ ζ a = x ∧ ∀ c ∈ Vx, ζ c ∈ Xfiber X c) :
    IsAsymptoticallySelfSimilar {c ∈ U | u c ∈ Xfiber X c} a (lam a)
      ((fun z => (deriv u a)⁻¹ * z) '' Xfiber X a) := by sorry
end MultibrotCorr
