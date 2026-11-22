-- Prove2me | Theorems.Thm_MultibrotCorr_theorem_5_1_closure
-- name    : MultibrotCorr.theorem_5_1_closure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T15:59:20.589174+00:00
-- url     : https://prove2.me/theorems/99292849-9f36-474d-883e-7203bcc98ba5
-- title:
--   Theorem 5.1 (Tan Lei), stated for the closure of $M_u$
-- statement:
--   Tan Lei's transfer theorem, as stated (simplified) in the paper. Let $u,\lambda$ be holomorphic on a neighborhood $U$ of $a$ with $u'(a)\ne0$, $u(a)=0$, $|\lambda(a)|>1$. Let $X$ be a closed subset of $U\times\mathbb{C}$ such that (i) for every $c$ near $a$, $0\in X(c)$ and $X(c)$ is $\lambda(c)$-self-similar about $0$ with a common radius $r$; and (ii) there is a dense subset $X'(a)\subset X(a)$ each of whose points extends to a holomorphic section $\zeta_x(c)\in X(c)$ near $a$. Then $M_u=\{c\in U:u(c)\in X(c)\}$ is asymptotically $\lambda(a)$-self-similar about $a$ with limit model $u'(a)^{-1}\cdot X(a)$.
--
--   **Formalization Note** The set $M_u=\{c\in U:u(c)\in X(c)\}$ is closed in $U$ but need not be closed in $\mathbb{C}$, while `IsAsymptoticallySelfSimilar` asks for a closed subset of $\mathbb{C}$. The conclusion is therefore stated for the closure of $M_u$ in $\mathbb{C}$. This changes nothing near $a$: the closure and $M_u$ agree on every closed disk about $a$ contained in $U$, and asymptotic self-similarity about $a$ only depends on the set near $a$. The closed subset $X$ of $U\times\mathbb{C}$ is given as the trace on $U\times\mathbb{C}$ of a closed subset of $\mathbb{C}^2$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Theorem 5.1, Section 5; citing Tan Lei, Similarity between the Mandelbrot set and Julia sets, Comm. Math. Phys. 134 (1990), Proposition 4.1, p. 601.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem theorem_5_1_closure (U : Set ℂ) (a : ℂ) (u lam : ℂ → ℂ) (X : Set (ℂ × ℂ))
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
    IsAsymptoticallySelfSimilar (closure {c ∈ U | u c ∈ Xfiber X c}) a (lam a)
      ((fun z => (deriv u a)⁻¹ * z) '' Xfiber X a) := by sorry
end MultibrotCorr
