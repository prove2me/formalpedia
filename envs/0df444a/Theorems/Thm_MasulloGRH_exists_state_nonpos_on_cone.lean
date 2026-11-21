-- Prove2me | Theorems.Thm_MasulloGRH_exists_state_nonpos_on_cone
-- name    : MasulloGRH.exists_state_nonpos_on_cone
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:46:39.661272+00:00
-- url     : https://prove2.me/theorems/2c664671-aba4-4ab1-9275-6aa5ecc6963c
-- title:
--   A convex cone of bounded functions with nonpositive infima admits a nonpositive state
-- statement:
--   Let $X$ be a set, $S\subseteq X$ a nonempty subset, and $K$ a convex cone of real functions on $X$ (closed under addition and under multiplication by nonnegative reals) such that
--
--   1. every $\varphi\in K$ is bounded on $S$;
--   2. every $\varphi\in K$ satisfies $\inf_{t\in S}\varphi(t)\le 0$, i.e. for every $\varepsilon>0$ there is $t\in S$ with $\varphi(t)\le\varepsilon$.
--
--   Then there is a **state** $\Lambda$ on the functions bounded on $S$ which is nonpositive on $K$: a map $\Lambda$ from real functions on $X$ to $\mathbb R$ which, on functions bounded on $S$, is additive, real-homogeneous and monotone with respect to the pointwise order on $S$, satisfies $\Lambda(1)=1$, and
--
--   $$\Lambda(\varphi)\le 0\qquad\text{for all }\varphi\in K.$$
--
--   This is the Hahn–Banach separation step in the proof of Pietsch's domination theorem: the cone $K$ is separated in $\ell^\infty(S)$ from the open cone of functions with strictly positive infimum, and the separating functional, suitably normalized, is the state.
--
--   **Formalization Note** $\Lambda$ is defined on all functions $X\to\mathbb R$, but its algebraic and order properties are only required for functions bounded on $S$ (values on unbounded functions are irrelevant).
-- source:
--   Pietsch domination theorem: A. Pietsch, Nuclear Locally Convex Spaces, Springer 1972, Theorem 2.3.3 and its proof (Hahn-Banach separation in the space of bounded functions); used for A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.2.4.10 (characterizations of nuclearity)

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem exists_state_nonpos_on_cone (X : Type*) (S : Set X) (hS : S.Nonempty)
    (K : Set (X → ℝ)) (hadd : ∀ φ ∈ K, ∀ ψ ∈ K, φ + ψ ∈ K)
    (hsmul : ∀ r : ℝ, 0 ≤ r → ∀ φ ∈ K, r • φ ∈ K)
    (hbdd : ∀ φ ∈ K, ∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M)
    (hinf : ∀ φ ∈ K, ∀ ε : ℝ, 0 < ε → ∃ t ∈ S, φ t ≤ ε) :
    ∃ Λ : (X → ℝ) → ℝ,
      (∀ φ ψ : X → ℝ, (∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) → (∃ M : ℝ, ∀ t ∈ S, |ψ t| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ) ∧
      (∀ (r : ℝ) (φ : X → ℝ), (∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) → Λ (r • φ) = r * Λ φ) ∧
      (∀ φ ψ : X → ℝ, (∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) → (∃ M : ℝ, ∀ t ∈ S, |ψ t| ≤ M) →
        (∀ t ∈ S, φ t ≤ ψ t) → Λ φ ≤ Λ ψ) ∧
      Λ (fun _ => 1) = 1 ∧ ∀ φ ∈ K, Λ φ ≤ 0 := by sorry

end MasulloGRH
