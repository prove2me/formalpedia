-- Prove2me | Theorems.Thm_MasulloGRH_hilbertian_of_pietsch_state
-- name    : MasulloGRH.hilbertian_of_pietsch_state
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:32:42.620659+00:00
-- url     : https://prove2.me/theorems/d8f5e602-015c-41fb-9a49-645518b66742
-- title:
--   Hilbertian 2-summing seminorm from a Pietsch state
-- statement:
--   Let $E$ be a complex Hausdorff locally convex space, $p,q$ continuous seminorms, $B$ the $q$-polar in $E'$, and let $\Lambda$ be a functional on real functions on $E'$ which on functions bounded on $B$ is additive, $\mathbb R$-homogeneous, monotone for the pointwise order on $B$, satisfies $\Lambda(1)=1$, and dominates $p$ in the sense $p(x)\le\Lambda(f\mapsto|f(x)|)$.
--
--   Then $$h(x)=\Lambda\big(f\mapsto |f(x)|^2\big)^{1/2}$$ (or some such seminorm) is a continuous Hilbertian seminorm with $p\le h\le q$, satisfying the parallelogram law, and $h$ is $2$-summing relative to $q$: whenever $\sum_i|f(x_i)|^2\le c$ for all $f\in B$, one has $\sum_i h(x_i)^2\le c$. The proof uses the Cauchy–Schwarz inequality for the positive functional $\Lambda$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C; Pietsch domination theorem (cf. A. Pietsch, Nuclear Locally Convex Spaces, Thm 2.3.3; Diestel-Jarchow-Tonge, Absolutely Summing Operators, Thm 2.12)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem hilbertian_of_pietsch_state (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (p q : Seminorm ℂ E) (hp : Continuous p) (hq : Continuous q)
    (Λ : (StrongDual ℂ E → ℝ) → ℝ)
    (hadd : ∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (r : ℝ) (φ : StrongDual ℂ E → ℝ),
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        Λ (r • φ) = r * Λ φ)
    (hmono : ∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → φ f ≤ ψ f) → Λ φ ≤ Λ ψ)
    (hone : Λ (fun _ => 1) = 1)
    (hdom : ∀ x : E, p x ≤ Λ (fun f => ‖f x‖)) :
    ∃ h : Seminorm ℂ E, Continuous h ∧ (∀ x, p x ≤ h x) ∧ (∀ x, h x ≤ q x) ∧
      (∀ x y, h (x + y) ^ 2 + h (x - y) ^ 2 = 2 * h x ^ 2 + 2 * h y ^ 2) ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
        ∑ i, h (x i) ^ 2 ≤ c := by sorry

end MasulloGRH
