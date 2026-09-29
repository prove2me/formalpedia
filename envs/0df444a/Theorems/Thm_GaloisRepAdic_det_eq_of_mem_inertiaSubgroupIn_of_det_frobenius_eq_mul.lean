-- Prove2me | Theorems.Thm_GaloisRepAdic_det_eq_of_mem_inertiaSubgroupIn_of_det_frobenius_eq_mul
-- name    : GaloisRepAdic.det_eq_of_mem_inertiaSubgroupIn_of_det_frobenius_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0fde000e-be0c-5195-83fc-8b1fe8853a6e
-- title:
--   Determinant on inertia at q from Frobenius determinants
-- statement:
--   Let $O$ be a commutative noetherian local ring which is an algebra over $\mathbb Z_p$ for a prime $p$, with $p$ lying in the maximal ideal of $O$. Let $M_0, q, c$ be natural numbers with $q$ prime, $q \nmid M_0$ and $q \neq p$, let $\varepsilon$ be a Dirichlet character modulo $M_0 q^c$ with values in $\mathbb C$, and let $S$ be a finite set of natural numbers. Let $R$ be a commutative ring equipped with an injective ring homomorphism $\mathrm{toC} \colon R \to \mathbb C$ and a ring homomorphism $\varphi \colon R \to O$, and let $e \colon \mathbb N \to R$ satisfy $\mathrm{toC}(e_\ell) = \varepsilon(\ell)$ for every prime $\ell$ with $\ell \nmid M_0 q^c$ and $\ell \notin S$. Let $\rho$ be an adic Galois representation over $O$: a free finite $O$-module $V$ with $\operatorname{rank}_O V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = (\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q})$ to $\mathrm{End}_O(V)$ which is adically continuous, in the sense that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every automorphism fixing $L$ pointwise acts on $V$ trivially modulo $\mathfrak m_O^n V$. Assume that for every prime $\ell$ with $\ell \nmid M_0 q^c$, $\ell \notin S$, $\ell \neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every automorphism $\tau$ lying in the decomposition subgroup of $A$ over $\mathbb Q$ and acting on the residue field of $A$ as $x \mapsto x^\ell$, one has $\det \rho(\tau) = \varphi(e_\ell)\cdot \ell$ in $O$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, and let $\sigma$ lie in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$. Let $u$ be a natural number with $u \equiv 1 \pmod{M_0}$ such that $\sigma \zeta = \zeta^u$ for every $\zeta \in \overline{\mathbb Q}$ with $\zeta^{q^c} = 1$, and let $\ell$ be a prime with $\ell \nmid M_0 q^c$, $\ell \notin S$ and $\ell \equiv u \pmod{M_0 q^c}$. Then $\det \rho(\sigma) = \varphi(e_\ell)$.
--
--   This is the identity $\det \rho = (\varepsilon \circ \kappa_{M_0q^c}) \cdot \chi_p$, for the mod-$M_0q^c$ and $p$-adic cyclotomic characters, evaluated at an element of the inertia group at $q \neq p$, where the $p$-adic factor is trivial and the mod-$M_0q^c$ cyclotomic character takes the value $u$; the value $\varphi(e_\ell) = \varepsilon(u)$ is recorded through an auxiliary prime $\ell \equiv u$. It is used in the construction of the $p$-adic representations attached to primitive cusp forms, to identify the determinant and the inertial behaviour at a prime dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_det_eq_of_mem_inertiaSubgroupIn_of_det_frobenius_eq_mul.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.det_eq_of_mem_inertiaSubgroupIn_of_det_frobenius_eq_mul
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] O] (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (M₀ q c : ℕ) (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀) (hqp : q ≠ p)
    (ε : DirichletCharacter ℂ (M₀ * q ^ c)) (S : Finset ℕ)
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O)
    (e : ℕ → R)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M₀ * q ^ c → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod (M₀ * q ^ c)))
    (ρ : GaloisRepAdic O)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M₀ * q ^ c → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.det (ρ.ρ τ) = φ (e ℓ) * (ℓ : O))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (u : ℕ) (hu₀ : u ≡ 1 [MOD M₀])
    (hcyc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ c) = 1 → σ ζ = ζ ^ u)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M₀ * q ^ c) (hℓS : ℓ ∉ S)
    (hℓu : ℓ ≡ u [MOD M₀ * q ^ c]) :
    LinearMap.det (ρ.ρ σ) = φ (e ℓ) := by sorry
