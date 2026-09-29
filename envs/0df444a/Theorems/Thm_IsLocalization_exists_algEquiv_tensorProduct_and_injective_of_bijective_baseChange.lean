-- Prove2me | Theorems.Thm_IsLocalization_exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange
-- name    : IsLocalization.exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c628b607-d367-5b15-92e2-056412fbec2e
-- title:
--   Generic fibre of a bijective base change widehat R⊗_R S→ T
-- statement:
--   Let $R$, $S$, $\widehat R$ be commutative domains, $T$ a commutative ring, and $K_1$, $K$, $E$ fields. Assume $S$ is an $R$-algebra that is finite as an $R$-module and has no zero $R$-smul divisors; $K_1$ is a fraction field of $R$ and $K$ a fraction field of $S$, with $K$ an $R$- and $K_1$-algebra making $R\to S\to K$ and $R\to K_1\to K$ towers. Assume $\widehat R$ is an $R$-algebra whose structure map is injective (faithful $R$-action) and flat as an $R$-module, $E$ is a fraction field of $\widehat R$, and $E$ carries compatible $R$- and $K_1$-algebra structures giving towers $R\to\widehat R\to E$ and $R\to K_1\to E$. Assume $T$ is simultaneously a $\widehat R$-algebra and an $S$-algebra over $R$, compatibly, and that the canonical $\widehat R$-algebra map $\widehat R\otimes_R S\to T$ determined by the two structure maps is bijective. Finally let $F_0$ be a commutative ring which is a $T$-algebra and a $\widehat R$-algebra compatibly, which is a localisation of $T$ at the image in $T$ of the non-zero-divisors of $\widehat R$, and which is an $E$-algebra with $\widehat R\to E\to F_0$ a tower. Then there is an isomorphism of $E$-algebras $e : E\otimes_{K_1}K \xrightarrow{\ \sim\ } F_0$ such that $e(1\otimes s)$ is the image of $s$ in $F_0$ through $T$, for every $s\in S$ (where $s$ is viewed in $K$); and the structure map $T\to F_0$ is injective.
--
--   This identifies the generic fibre of a ring $T$ obtained by a flat base change $\widehat R\otimes_R S$ of a module-finite extension of domains: inverting the non-zero-divisors of $\widehat R$ turns $T$ into the tensor product $E\otimes_{K_1}K$ of the fraction fields, compatibly with $S\to K$, and $T$ embeds in it. It is used, before $T$ is known to be a domain, to transport torsion-freeness, reducedness and separability properties of $E\otimes_{K_1}K$ to $T$; it is cited in the description of the adic completion of the local model of a modular curve at a crossing point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalization_exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalization.exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange
    {R S Rhat T K₁ K E : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [CommRing Rhat] [IsDomain Rhat]
    [CommRing T] [Field K₁] [Field K] [Field E]

    [Algebra R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra S K] [IsFractionRing S K]
    [Algebra R K] [Algebra K₁ K] [IsScalarTower R S K] [IsScalarTower R K₁ K]

    [Algebra R Rhat] [FaithfulSMul R Rhat] [Module.Flat R Rhat]
    [Algebra Rhat E] [IsFractionRing Rhat E]
    [Algebra R E] [Algebra K₁ E] [IsScalarTower R Rhat E] [IsScalarTower R K₁ E]

    [Algebra Rhat T] [Algebra S T] [Algebra R T] [IsScalarTower R Rhat T] [IsScalarTower R S T]
    (hT : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId Rhat T) (IsScalarTower.toAlgHom R S T)
        (fun _ _ => Commute.all _ _) : Rhat ⊗[R] S →ₐ[Rhat] T))

    (F₀ : Type*) [CommRing F₀] [Algebra T F₀] [Algebra Rhat F₀] [IsScalarTower Rhat T F₀]
    [IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors Rhat)) F₀]
    [Algebra E F₀] [IsScalarTower Rhat E F₀] :
    (∃ e : (E ⊗[K₁] K) ≃ₐ[E] F₀,
      ∀ s : S, e ((1 : E) ⊗ₜ[K₁] algebraMap S K s) = algebraMap T F₀ (algebraMap S T s)) ∧
    Function.Injective (algebraMap T F₀) := by sorry
