-- Prove2me | Theorems.Thm_LeblSCV_Levi_tomato_can
-- name    : LeblSCV.Levi.tomato_can
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:32:33.154931+00:00
-- url     : https://prove2.me/theorems/fe5a3ef1-3afe-4c87-ab97-4bd8fdf2c4cf
-- title:
--   Theorem 2.3.11 — Tomato can principle
-- statement:
--   Let $U \subset \mathbb{C}^n$ be an open set with smooth boundary and $p \in \partial U$, and suppose the Levi form has a negative eigenvalue at $p$: for a defining function $r$ of $U$ at $p$ (with $r < 0$ on $U$) there is $X_p = \sum_k a_k \frac{\partial}{\partial z_k}\big|_p \in T^{(1,0)}_p\partial U$ with
--   $$\mathcal{L}(X_p, X_p) = \sum_{k,\ell=1}^n \bar a_k a_\ell \left.\frac{\partial^2 r}{\partial \bar z_k \partial z_\ell}\right|_p < 0 .$$
--   Then every holomorphic function on $U$ extends to a neighbourhood of $p$: there is a connected open $W \ni p$ such that every $f \in \mathcal{O}(U)$ agrees on $U \cap W$ with some $F \in \mathcal{O}(W)$. In particular, if $U$ is connected, $U$ is not a domain of holomorphy.
--
--   This is the easy direction of the Levi problem: a domain of holomorphy with smooth boundary is pseudoconvex.
--
--   **Formalization Note.** Holomorphic is `DifferentiableOn ℂ`; $\mathbb{C}^n$ is `Fin n → ℂ`. The negative eigenvalue is asserted for one defining function; by Proposition 2.3.6 it then holds for all. $W$ is chosen before $f$, so it is the same for every $f$, as in Definition 2.1.1; "extends" means $F = f$ on the whole overlap $U \cap W$. Definition 2.1.1 applies only to domains, so the second conjunct adds the hypothesis that $U$ is connected.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 75, Theorem 2.3.11

import Mathlib
import Definitions.Def_LeblSCV_Shared_IsDomainOfHolomorphy
import Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
import Definitions.Def_LeblSCV_Levi_holTangent
import Definitions.Def_LeblSCV_Levi_leviForm

namespace LeblSCV.Levi

/-- Theorem 2.3.11 (Tomato can principle; Lebl, p. 75). If `U ⊆ ℂⁿ` is open with smooth boundary,
`p ∈ ∂U`, and for a defining function `r` of `U` at `p` the Levi form takes a negative value on
some `X_p ∈ T_p^{(1,0)} ∂U` (the Levi form has a negative eigenvalue), then every holomorphic
function on `U` extends to a neighbourhood of `p`: there is a connected open `W ∋ p` such that
every holomorphic `f` on `U` agrees on `U ∩ W` with a holomorphic `F` on `W`; in particular a
connected such `U` is not a domain of holomorphy. -/
theorem tomato_can {n : ℕ} (U : Set (Fin n → ℂ)) (hU : HasSmoothBoundary U)
    (p : Fin n → ℂ) (hp : p ∈ frontier U)
    (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) (hr : IsDefiningFunction U p V r)
    (hneg : ∃ a ∈ holTangent r p, (leviForm r p a).re < 0) :
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ IsConnected W ∧ p ∈ W ∧
      ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
        ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W)) ∧
    (IsConnected U → ¬ LeblSCV.Shared.IsDomainOfHolomorphy U) := by sorry

end LeblSCV.Levi
