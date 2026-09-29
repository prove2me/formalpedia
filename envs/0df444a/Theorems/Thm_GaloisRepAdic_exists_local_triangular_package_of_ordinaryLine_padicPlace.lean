-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_local_triangular_package_of_ordinaryLine_padicPlace
-- name    : GaloisRepAdic.exists_local_triangular_package_of_ordinaryLine_padicPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a7c2653e-b5e9-5a86-86f0-c9f16b98b7f9
-- title:
--   Upper-triangular local package for an ordinary line at p
-- statement:
--   Let $B$ be a finite commutative local ring and $p$ a prime. Let $\rho$ be an adic Galois representation over $B$: a free finite $B$-module $V$ of rank $2$ together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_B V$ whose action is adically continuous (for each $n$ some finite subextension acts trivially modulo $\mathfrak m_B^n V$). Assume the determinant is cyclotomic at $p$: $p \in \mathfrak m_B$, and whenever $\sigma$ acts on the $p^n$-th roots of unity of $\overline{\mathbb Q}$ by $\mu \mapsto \mu^a$ one has $\det \rho.\rho(\sigma) \equiv a \pmod{p^n}$. Let $b = (b_0,b_1)$ be a $B$-basis of $V$ such that every $\sigma$ in the decomposition subgroup of the place [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) over $\mathbb Q$ sends $b_0$ into $B b_0$, and every $\sigma$ in the image `inertiaSubgroupIn` of the corresponding inertia subgroup acts trivially on $V/Bb_0$. Let $t \in B$ be such that every scalar $z$ by which some decomposition-group element acts on $V/Bb_0$ satisfies $z^2-1 \in (t)$, and assume at least one such scalar has $z^2 \neq 1$. Assume finally that [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) carries the inertia subgroup of [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) over $\mathbb Q_p$ into the global inertia subgroup at [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25), and that every decomposition-group element has the same image under $\rho.\rho$ as the global image of some $g \in \mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$. Then there exist functions $x,z$ from $\mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$ to $B^\times$ and $y$ to $B$, and an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ finite over $\mathbb Q$, such that for all local $g$ one has $\rho.\rho(\mathrm{localGaloisToGlobal}\ p\ g)(b_0) = x(g)b_0$ and $\rho.\rho(\mathrm{localGaloisToGlobal}\ p\ g)(b_1) = y(g)b_0 + z(g)b_1$; $x$ and $z$ are multiplicative and $y(gh) = x(g)y(h) + y(g)z(h)$; $(x,y,z)(s) = (1,0,1)$ whenever the global image of $s$ lies in the fixing subgroup of $F$; $z(\tau) = 1$ for $\tau$ in the inertia subgroup of [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) over $\mathbb Q_p$; $x(g)z(g) \equiv a \pmod{p^n}$ whenever $g$ acts on the $p^n$-th roots of unity of $\overline{\mathbb Q}_p$ by $\mu \mapsto \mu^a$; $z(g)^2 - 1 \in (t)$ for all $g$; and $z(g)^2 \neq 1$ for at least one $g$.
--
--   This packages an ordinary (upper-triangular) line at $p$ into explicit matrix coordinates: two multiplicative characters $x,z$ along the diagonal, a crossed-homomorphism entry $y$, a finite level $F$ on which the package is trivial, unramifiedness of the quotient character on local inertia, and the transport of both the cyclotomic determinant congruence and the two congruence conditions attached to $t$ from the global decomposition group to $\mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$. It is used by [`GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle`](thm.html#GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle), in the local analysis of très ramifiée classes at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_local_triangular_package_of_ordinaryLine_padicPlace.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_local_triangular_package_of_ordinaryLine_padicPlace
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (ρ : GaloisRepAdic B) (hdet : ρ.DetIsCyclotomic p)
    (b : Module.Basis (Fin 2) B ρ.V)
    (hLD : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ B ∙ b 0)
    (hLI : ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ B ∙ b 0)
    (t : B)
    (hsq : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∀ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) → z * z - 1 ∈ Ideal.span {t})
    (hne : ∃ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∃ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) ∧ z * z ≠ 1)
    (hIloc : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ)
    (hsur : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ,
      ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) = ρ.ρ σ) :
    ∃ (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) (b 0) = (x g : B) • b 0) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) (b 1) = y g • b 0 + (z g : B) • b 1) ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h) ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h) ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B)) ∧
      (∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1) ∧
      (∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1) ∧
      (∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)}) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ Ideal.span {t}) ∧
      (∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) ≠ 1) := by sorry
