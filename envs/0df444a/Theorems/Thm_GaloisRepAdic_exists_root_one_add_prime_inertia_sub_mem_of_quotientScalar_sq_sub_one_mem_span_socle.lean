-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle
-- name    : GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/8407bdca-0fad-5acf-a177-6875bbf277f2
-- title:
--   Socle thickening forces residual peu-ramifié splitting by (1+p)^{1/p}
-- statement:
--   Let $B$ be a finite commutative local ring with maximal ideal $\mathfrak m$, let $p$ be an odd prime, and let $\rho$ be an adic Galois representation over $B$: a finite free $B$-module $V$ with $\operatorname{rank}_B V = 2$ together with a monoid homomorphism $\rho.\rho$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_B V$ that is adically continuous (for every $n$ some finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ has its fixing subgroup acting trivially on $V$ modulo $\mathfrak m^n V$). Assume the determinant is cyclotomic at $p$: $p \in \mathfrak m$, and whenever $\sigma$ raises all $p^n$-th roots of unity to the $a$-th power, $\det \rho(\sigma) - a \in (p^n)$. Fix a basis $b_0, b_1$ of $V$ such that $B b_0$ is stable under $\rho$ of the decomposition subgroup of the place [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) (the valuation subring of $\overline{\mathbb Q}$ pulled back from the valuation subring of $\overline{\mathbb Q}_p$ along a fixed embedding), and such that every $\sigma$ in the inertia subgroup of that place, viewed inside the full Galois group, satisfies $\rho(\sigma)v - v \in B b_0$ for all $v$. Let $t \in \mathfrak m$ with $t\mathfrak m = 0$. Suppose every $z \in B$ that is a quotient scalar for some $\sigma$ in the decomposition subgroup, in the sense that $\rho(\sigma)v - z v \in B b_0$ for all $v$, satisfies $z^2 - 1 \in (t)$, and that some quotient scalar $z$ of some decomposition element has $z^2 \neq 1$. Then there exists $\beta$ in the algebraic closure `PadicAlgCl p` of $\mathbb Q_p$ with $\beta^p = 1 + p$ such that for every $\tau \in \operatorname{Aut}_{\mathbb Q_p}(\overline{\mathbb Q}_p)$ lying in the inertia subgroup of the $p$-adic valuation subring, fixing every $\xi$ with $\xi^p = 1$ and fixing $\beta$, the image of $\tau$ under [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) acts trivially modulo $\mathfrak m$: $\rho(\tau)v - v \in \mathfrak m \cdot V$ for all $v \in V$.
--
--   This is the local analysis at $p$ in the style of Wiles's Proposition 1.1(ii): a non-strict thickening of an ordinary line by a socle element $t$ of the finite local coefficient ring forces the residual representation to be peu ramifiée at $p$, in Serre's explicit form where the inertia action is split by the $p$-th root of the unit $1+p$ (which generates $\mathbb Z_p^\times/(\mathbb Z_p^\times)^p$ for odd $p$). It is used to prove that quotient scalars of decomposition elements square to $1$ once the residual representation is known not to be peu ramifiée (très ramifiée).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic B) (hdet : ρ.DetIsCyclotomic p)
    (b : Module.Basis (Fin 2) B ρ.V)
    (hLD : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ B ∙ b 0)
    (hLI : ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ B ∙ b 0)
    (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (hsq : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∀ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) → z * z - 1 ∈ Ideal.span {t})
    (hne : ∃ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∃ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) ∧ z * z ≠ 1) :
    ∃ β : PadicAlgCl p, β ^ p = 1 + (p : PadicAlgCl p) ∧
      ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          ∀ v : ρ.V, ρ.ρ (localGaloisToGlobal p τ) v - v ∈
            (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V) := by sorry
