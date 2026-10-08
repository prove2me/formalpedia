-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_exists_maximizer_mem_Icc
-- name    : NonlinSSD.DualFunctional.exists_maximizer_mem_Icc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:13:30.184126+00:00
-- url     : https://prove2.me/theorems/b5aba306-6a1d-48c2-88e9-0843599382a1
-- title:
--   Proof of Theorem 4, p. 13 — for 0 ≤ ξ ≤ v′₋(a), v(t) − ξt has a maximizer in [a, b], so v^*(ξ) is finite
-- statement:
--   Let $a\le b$, $v\in\mathcal U_1([a,b])$ and let $\xi$ be a real number with
--   $$0\le\xi\le v'_-(a).$$
--   Then the function $t\mapsto v(t)-\xi t$ attains its maximum over $\mathbb R$ at some point $t_0\in[a,b]$:
--   $$v(t)-\xi t\le v(t_0)-\xi t_0\quad\text{for all } t\in\mathbb R,$$
--   and consequently the concave conjugate is finite, $v^*(\xi)=\xi t_0-v(t_0)$.
--
--   This is the pointwise fact behind the finite case of Theorem 4: on the domain $0\le\zeta\le v'_-(a)$, the inner maximization defining $-v^*(\zeta(\omega))$ can be restricted to the compact interval $[a,b]$.
--
--   **Formalization Note** The paper states this for the random variable $\zeta$ almost surely; here it is stated for a deterministic $\xi$, which is the content of "the function $v(t)-\zeta t$ has a maximizer in $[a,b]$" at each $\omega$. $v^*$ is `EReal`-valued, and the conclusion gives its value as a real number.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 13, proof of Theorem 4

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem exists_maximizer_mem_Icc (a b : ℝ) (hab : a ≤ b) (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξc : ξ ≤ leftDeriv v a) :
    ∃ t₀ ∈ Set.Icc a b, (∀ t : ℝ, v t - ξ * t ≤ v t₀ - ξ * t₀) ∧
      concaveConj v ξ = ((ξ * t₀ - v t₀ : ℝ) : EReal) := by sorry

end NonlinSSD.DualFunctional
