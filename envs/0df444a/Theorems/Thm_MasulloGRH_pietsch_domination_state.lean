-- Prove2me | Theorems.Thm_MasulloGRH_pietsch_domination_state
-- name    : MasulloGRH.pietsch_domination_state
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:32:33.604194+00:00
-- url     : https://prove2.me/theorems/42490871-482c-4f79-8c82-d43242b4855c
-- title:
--   Pietsch domination: a normalized positive state on the $q$-polar
-- statement:
--   Let $E$ be a complex topological vector space and $p,q$ seminorms on $E$, and let $B=\{f\in E' : |f(y)|\le q(y)\ \forall y\}$ be the $q$-polar in the continuous dual. Assume the absolutely summing inequality: for every finite family $x_1,\dots,x_n$ and every $c$, if $\sum_i |f(x_i)|\le c$ for all $f\in B$ then $\sum_i p(x_i)\le c$.
--
--   Then there is a *Pietsch state* $\Lambda$ on real functions on $E'$ which, restricted to functions bounded on $B$, is additive, $\mathbb R$-homogeneous, monotone with respect to the pointwise order on $B$, normalized by $\Lambda(1)=1$, and dominates $p$: $$p(x)\le \Lambda\big(f\mapsto |f(x)|\big)\quad\text{for all }x\in E.$$ This is the Hahn–Banach form of the Pietsch domination theorem (a positive normalized functional on $\ell^\infty(B)$ replaces the Pietsch probability measure).
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C; Pietsch domination theorem (cf. A. Pietsch, Nuclear Locally Convex Spaces, Thm 2.3.3; Diestel-Jarchow-Tonge, Absolutely Summing Operators, Thm 2.12)

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem pietsch_domination_state (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p q : Seminorm ℂ E)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) :
    ∃ Λ : (StrongDual ℂ E → ℝ) → ℝ,
      (∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ) ∧
      (∀ (r : ℝ) (φ : StrongDual ℂ E → ℝ),
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        Λ (r • φ) = r * Λ φ) ∧
      (∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → φ f ≤ ψ f) → Λ φ ≤ Λ ψ) ∧
      Λ (fun _ => 1) = 1 ∧
      ∀ x : E, p x ≤ Λ (fun f => ‖f x‖) := by sorry

end MasulloGRH
