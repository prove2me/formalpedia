-- Prove2me | Theorems.Thm_MasulloGRH_adelicThetaHomogeneous_estimates
-- name    : MasulloGRH.adelicThetaHomogeneous_estimates
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T04:35:35.90048+00:00
-- url     : https://prove2.me/theorems/74b2596a-6685-4012-8e92-4160d3e55047
-- title:
--   Theorem 2.2.5.4 — estimates for the $\omega$-homogeneous $\theta$-function $\Phi_{F,\omega}(f)$, uniform on bounded sets
-- statement:
--   Let $F$ be a number field, $\chi$ a Hecke character and $\omega=\chi|_{C_F^1}$. For $f\in\mathcal S(\mathbb A_F)$ let
--   $$\Phi_{F,\omega}(f)(g)=\int_{C_F^1}\Phi_F(f)(hg)\,\omega(h)\,d\mu_1(h)$$
--   be the $\omega$-homogeneous $\theta$-function, with $\mu_1$ the Tamagawa measure on $C_F^1$ of total mass $\mu_1(C_F^1)$, and let $\delta_\omega=1$ if $\omega$ is trivial and $\delta_\omega=0$ otherwise.
--
--   1. $\Phi_{F,\omega}(f)$ is continuous, and $\Phi_{F,\omega}(f)(hg)=\omega(h)^{-1}\Phi_{F,\omega}(f)(g)$ for every idele $h$ of norm $1$.
--   2. Let $B\subset\mathcal S(\mathbb A_F)$ be bounded and $N\ge0$ an integer. There is a constant $C>0$ such that for all $f\in B$ and all ideles $g$:
--      - if $\log|g|_F>1$, then $|\Phi_{F,\omega}(f)(g)|\le C\,|g|_F^{-N}$;
--      - if $\log|g|_F<-1$, then
--      $$\Big|\Phi_{F,\omega}(f)(g)-\big(|g|_F^{-1}\mu_1(C_F^1)\,\widehat f(0)-\mu_1(C_F^1)\,f(0)\big)\delta_\omega\Big|\le C\,|g|_F^{N};$$
--      - if $f(0)=\widehat f(0)=0$ or $\omega$ is non-trivial, and $|\log|g|_F|>1$, then
--      $$|\Phi_{F,\omega}(f)(g)|\le C\,e^{-N|\log|g|_F|}.$$
--
--   So the isotypic components of a $\theta$-function with $\omega\neq1$ decay exponentially in both directions; this is why the Mellin transform is entire on the components of $\Omega(C_F)$ other than the principal one.
--
--   **Formalization Note** $\omega$ is given as the restriction of a Hecke character $\chi$. Item 1 states the homogeneity as an explicit identity. Item 2 is the uniform form of parts (5)–(6) of the source with threshold $1$; the three constants are stated separately. The compatibility with differential operators, part (3) of the source, is not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.2.5.1, Theorem 2.2.5.4 (Estimates over the idele classes - II), parts (1), (2), (4) in the uniform form of parts (5)–(6), eqs. (2.2.5.9), (2.2.5.10), (2.2.5.12), pp. 97–98; Definition 2.2.5.1, p. 95

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain
open Classical

theorem adelicThetaHomogeneous_estimates (F : Type*) [Field F] [NumberField F]
    (χ : HeckeCharacter F) :
    (∀ f : AdelicSchwartz F, Continuous (adelicThetaHomogeneous χ f) ∧
      ∀ h g : IdeleGroup F, ideleNorm h = 1 →
        adelicThetaHomogeneous χ f (h * g) =
          ((χ (QuotientGroup.mk h) : Circle) : ℂ)⁻¹ * adelicThetaHomogeneous χ f g) ∧
    (∀ B : Set (AdelicSchwartz F), Bornology.IsVonNBounded ℂ B → ∀ N : ℕ,
      (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, 1 < Real.log (ideleNorm g) →
        ‖adelicThetaHomogeneous χ f g‖ ≤ C * ideleNorm g ^ (-(N : ℤ))) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, Real.log (ideleNorm g) < -1 →
        ‖adelicThetaHomogeneous χ f g -
            (if χ.IsTrivialOnNormOne then
              ((ideleNorm g)⁻¹ : ℝ) * (tamagawaClassVolume F : ℂ) * adelicFourier f 0 -
                (tamagawaClassVolume F : ℂ) * f.eval 0
            else 0)‖ ≤ C * ideleNorm g ^ N) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, (f.IsPolarFree ∨ ¬ χ.IsTrivialOnNormOne) →
        ∀ g : IdeleGroup F, 1 < |Real.log (ideleNorm g)| →
          ‖adelicThetaHomogeneous χ f g‖ ≤ C * Real.exp (-(N * |Real.log (ideleNorm g)|)))) := by sorry

end MasulloGRH
