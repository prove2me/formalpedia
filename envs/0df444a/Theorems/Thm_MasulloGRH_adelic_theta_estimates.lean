-- Prove2me | Theorems.Thm_MasulloGRH_adelic_theta_estimates
-- name    : MasulloGRH.adelic_theta_estimates
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T04:34:34.943984+00:00
-- url     : https://prove2.me/theorems/78892f7b-5c45-49e5-b63d-8a0136d9aab9
-- title:
--   Theorem 2.2.3.4 — estimates for $\Phi_F(f)$ over the idele classes, uniform on bounded sets
-- statement:
--   Let $F$ be a number field. For $f\in\mathcal S(\mathbb A_F)$ let $\Phi_F(f)(g)=\sum_{\xi\in F^\times}f(\xi g)$ be the adelic $\theta$-function and $\widehat f$ the adelic Fourier transform.
--
--   Let $B\subset\mathcal S(\mathbb A_F)$ be a bounded subset and $N\ge0$ an integer. Then there is a constant $C>0$, depending on $B$ and $N$, such that for every $f\in B$ and every idele $g$:
--
--   1. if $|g|_F>1$, then
--   $$|\Phi_F(f)(g)|\le C\,|g|_F^{-N};$$
--   2. if $|g|_F<1$, then
--   $$\big|\Phi_F(f)(g)-|g|_F^{-1}\widehat f(0)+f(0)\big|\le C\,|g|_F^{N};$$
--   3. if $f(0)=\widehat f(0)=0$ and $|g|_F\neq1$, then
--   $$|\Phi_F(f)(g)|\le C\,e^{-N|\log|g|_F|}.$$
--
--   So $\Phi_F(f)$ decays faster than every power of $|g|_F^{-1}$ at infinity, is asymptotic to $|g|_F^{-1}\widehat f(0)-f(0)$ at $0$, and decays exponentially in $|\log|g|_F|$ in both directions when $f\in\mathcal S_0(\mathbb A_F)$, uniformly for $f$ in a bounded set.
--
--   **Formalization Note** The statement is the uniform form of parts (4)–(5) of the source with threshold $T_{B,N}=1$; a single $f$ is the bounded set $\{f\}$. The three constants are stated separately.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.2.3.1, Theorem 2.2.3.4 (Estimates over the Idele Classes - I), eqs. (2.2.3.4)–(2.2.3.6), pp. 82–83, in the uniform form of parts (4)–(5)

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem adelic_theta_estimates (F : Type*) [Field F] [NumberField F]
    (B : Set (AdelicSchwartz F)) (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, 1 < ideleNorm g →
      ‖adelicTheta f g‖ ≤ C * ideleNorm g ^ (-(N : ℤ))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, ideleNorm g < 1 →
      ‖adelicTheta f g - ((ideleNorm g)⁻¹ : ℝ) * adelicFourier f 0 + f.eval 0‖ ≤
        C * ideleNorm g ^ N) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, f.IsPolarFree → ∀ g : IdeleGroup F, ideleNorm g ≠ 1 →
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N * |Real.log (ideleNorm g)|))) := by sorry

end MasulloGRH
