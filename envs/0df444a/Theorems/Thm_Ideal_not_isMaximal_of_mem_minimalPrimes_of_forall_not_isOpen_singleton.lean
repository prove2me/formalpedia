-- Prove2me | Theorems.Thm_Ideal_not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton
-- name    : Ideal.not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/d4eb1502-4952-5f2f-bc64-6ead8e82dd0e
-- title:
--   Minimal primes of the special fibre are not maximal
-- statement:
--   Let $R$ be a commutative ring and $\kappa$ a field equipped with an $R$-algebra structure, and let $\varpi \in R$ be an element whose image in $\kappa$ under the structure map is $0$ and such that the principal ideal $(\varpi) = \mathrm{span}\{\varpi\}$ is a maximal ideal of $R$. Let $B$ be a commutative $R$-algebra which is of finite type over $R$, and let $b \in B$ be the image $\varpi \cdot 1$ of $\varpi$ under the structure map $R \to B$. Assume that no point of $\operatorname{Spec}(B \otimes_R \kappa)$ is isolated, i.e. for every prime $z$ of $B \otimes_R \kappa$ the singleton $\{z\}$ is not open in the prime spectrum. Then for every ideal $Q$ of the quotient $B/(b)$ which is a minimal prime of that ring (a minimal element, for inclusion, of the set of prime ideals of $B/(b)$, i.e. a member of `minimalPrimes (B ⧸ Ideal.span {b})`), the ideal $Q$ is not maximal.
--
--   The statement combines Zariski's lemma with base change along $R/(\varpi) \hookrightarrow \kappa$: isolated points of $\operatorname{Spec}(B \otimes_R \kappa)$ are what a minimal prime of the special fibre $B/\varpi B$ that happened also to be maximal would produce, so their absence forces every minimal prime of $B/\varpi B$ to be non-maximal. It is used in the analysis of stalks of the Igusa scheme, for [`ModularCurve.IgusaScheme.free_localizedModule_sections_of_isRegularLocalRing_stalk_of_isFinite`](thm.html#ModularCurve.IgusaScheme.free_localizedModule_sections_of_isRegularLocalRing_stalk_of_isFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

theorem Ideal.not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton
    {R : Type*} [CommRing R] {κ : Type*} [Field κ] [Algebra R κ]
    (ϖ : R) (hϖ : algebraMap R κ ϖ = 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (b : B) (hb : b = algebraMap R B ϖ)
    (hiso : ∀ z : PrimeSpectrum (B ⊗[R] κ), ¬ IsOpen ({z} : Set (PrimeSpectrum (B ⊗[R] κ))))
    (Q : Ideal (B ⧸ Ideal.span {b})) (hQ : Q ∈ minimalPrimes (B ⧸ Ideal.span {b})) :
    ¬ Q.IsMaximal := by sorry
