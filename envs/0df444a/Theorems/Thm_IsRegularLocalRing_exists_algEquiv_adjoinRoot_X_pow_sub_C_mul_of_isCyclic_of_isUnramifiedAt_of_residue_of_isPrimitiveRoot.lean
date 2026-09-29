-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
-- name    : IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/b29444ca-4053-5f34-955f-22f3214b9173
-- title:
--   Abhyankar's lemma: cyclic covers unramified off s are Kummer
-- statement:
--   Let $R$ be a regular local domain that is complete for the $\mathfrak m_R$-adic topology, with $\mathfrak m_R = (\varpi, s)$ for two given elements $\varpi, s \in R$ and with $\operatorname{ringKrullDim} R = 2$. Let $e \geq 1$ be an integer whose image in $R$ is a unit, and suppose $R$ contains an element $\zeta$ that is a primitive $e$-th root of unity. Let $B$ be an integrally closed Noetherian local domain which is an $R$-algebra, module-finite over $R$ and such that $R$ acts faithfully (so $R \to B$ is injective), let $K_0$ be a fraction field of $R$ and $F$ a fraction field of $B$, with $F$ a field extension of $K_0$ compatibly with the maps from $R$ and $B$; assume $F/K_0$ is finite Galois with cyclic Galois group and $[F : K_0] = e$. Assume further that for every prime $\mathfrak p$ of $B$ whose contraction to $R$ has height $1$ and does not contain $s$, the algebra $B$ is unramified over $R$ at $\mathfrak p$, and that the residue extension is trivial in the strong form: every $b \in B$ satisfies $b - \operatorname{algebraMap}_{R,B}(r) \in \mathfrak m_B$ for some $r \in R$. Then there exists a unit $u \in R^\times$ and an isomorphism of $R$-algebras $B \cong R[X]/(X^e - u s)$.
--
--   This is Abhyankar's lemma in the local form used for cyclic covers of a two-dimensional regular local base containing the $e$-th roots of unity: a normal cyclic cover of degree $e$ that is unramified away from the regular divisor $s = 0$ and has trivial residue extension is the Kummer cover obtained by extracting an $e$-th root of a unit multiple of $s$. It feeds the variant of the same statement in which the presence of a primitive $e$-th root of unity in $R$ is not assumed outright.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ e)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = e)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R B) → Algebra.IsUnramifiedAt R 𝔭)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B) :
    ∃ u : Rˣ, Nonempty (B ≃ₐ[R] AdjoinRoot (X ^ e - C ((u : R) * s) : R[X])) := by sorry
