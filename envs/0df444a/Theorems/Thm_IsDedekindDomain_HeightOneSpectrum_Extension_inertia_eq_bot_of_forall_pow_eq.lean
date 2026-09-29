-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_forall_pow_eq
-- name    : IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_forall_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/7cda7aaf-27c5-53fe-a1cc-8d80348ff566
-- title:
--   Trivial inertia in multi-radical extensions above v ∤ n
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, let $\iota$ be an index type and $n$ a natural number, and let $u \colon \iota \to E$ and $\alpha \colon \iota \to M$ be families such that $\alpha_i^{\,n}$ is the image of $u_i$ under the structure map $E \to M$ for every $i$. Assume that $M$ is generated over $E$ by the $\alpha_i$ in the weak sense that every $E$-algebra automorphism $\sigma$ of $M$ fixing all the $\alpha_i$ equals the identity. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_E$, and assume that the $v$-adic valuation of each $u_i$ equals $1$, and that the image of $n$ in $\mathcal{O}_E$ does not lie in the prime ideal $v$. Finally let $w$ be an extension of $v$ to $\mathcal{O}_M$, that is, a height-one prime of $\mathcal{O}_M$ whose contraction to $\mathcal{O}_E$ is $v$. The conclusion is that the inertia subgroup of the automorphism group $M \simeq_{\mathrm{alg}[E]} M$ at the prime ideal of $w$ is trivial. No separability, normality or Galois hypothesis on $M/E$ is imposed, and nothing is asserted about the ramification index itself.
--
--   This is the statement that a multi-radical (Kummer-type) extension $E(u_i^{1/n} : i \in \iota)$ has trivial inertia above each finite place $v$ of $E$ at which all the $u_i$ are units and which does not divide $n$; when $M/E$ is Galois it says exactly that $v$ is unramified in $M$. It is used in the algebraic proof of the second inequality of class field theory, via [`NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots`](thm.html#NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots), where $M$ is obtained by adjoining $p$-th roots of a group of $S$-units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_forall_pow_eq.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_forall_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {ι : Type*} {n : ℕ} (u : ι → E) (α : ι → M) (hα : ∀ i, α i ^ n = algebraMap E M (u i))
    (hgen : ∀ σ : M ≃ₐ[E] M, (∀ i, σ (α i) = α i) → σ = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hu : ∀ i, v.valuation E (u i) = 1)
    (hnv : ((n : ℕ) : NumberField.RingOfIntegers E) ∉ v.asIdeal)
    (w : v.Extension (NumberField.RingOfIntegers M)) :
    w.1.asIdeal.inertia (M ≃ₐ[E] M) = ⊥ := by sorry
