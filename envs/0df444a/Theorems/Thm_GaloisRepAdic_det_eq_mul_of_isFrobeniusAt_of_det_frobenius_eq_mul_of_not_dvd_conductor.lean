-- Prove2me | Theorems.Thm_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor
-- name    : GaloisRepAdic.det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0f44d440-e65e-5e4d-a1b2-aad12cc7da20
-- title:
--   Determinant at a Frobenius above q from a congruent prime
-- statement:
--   Let $O$ be a noetherian local commutative ring that is a $\mathbb{Z}_p$-algebra for a prime $p$, with $p$ lying in the maximal ideal of $O$. Let $M_0$ and a prime $q \nmid M_0$ with $q \neq p$ be given, let $\varepsilon$ be a complex Dirichlet character modulo $M_0 q$ whose conductor is not divisible by $q$, and let $S$ be a finite set of natural numbers. Let $R$ be a commutative ring equipped with an injective ring homomorphism $\mathrm{toC} : R \to \mathbb{C}$ and a ring homomorphism $\varphi : R \to O$, and let $e : \mathbb{N} \to R$ satisfy $\mathrm{toC}(e_\ell) = \varepsilon(\ell \bmod M_0 q)$ for every prime $\ell \nmid M_0 q$ with $\ell \notin S$. Let $\rho$ be an adic Galois representation over $O$, that is, a free finite $O$-module $V$ of rank $2$ together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{End}_O(V)$ which is continuous for the maximal-adic filtration, in the sense that for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every automorphism fixing $L$ pointwise acts on $V$ by an endomorphism congruent to the identity modulo $\mathfrak{m}_O^n \cdot V$. Assume that for every prime $\ell \nmid M_0 q$ with $\ell \notin S$ and $\ell \neq p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\tau$ in the decomposition subgroup of $A$ acting as $x \mapsto x^{\ell}$ on the residue field of $A$, one has $\det(\rho.\rho\,\tau) = \varphi(e_\ell) \cdot \ell$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $q$ is a non-unit and let $\tau$ lie in the decomposition subgroup of $P$ and act as $x \mapsto x^{q}$ on the residue field of $P$. Then for every prime $\ell \nmid M_0 q$ with $\ell \notin S$ and $\ell \equiv q \pmod{M_0}$, $\det(\rho.\rho\,\tau) = \varphi(e_\ell) \cdot q$ in $O$.
--
--   This is the evaluation at a Frobenius element above the prime $q$ of the determinant identity $\det\rho = (\varepsilon \circ \kappa_{M_0 q}) \cdot \chi_p$, with the value of the nebentypus at $q$ read off from any auxiliary prime $\ell$ congruent to $q$ modulo $M_0$, the conductor condition making $\varepsilon$ insensitive to the $q$-part. It supplies the determinant, and hence the second eigenvalue, in the description of the Frobenius action at $q$ on the Galois representation of a newform of level exactly divisible by $q$ with nebentypus unramified at $q$, and is used in [`GaloisRepAdic.charpoly_eq_of_isFrobeniusAt_of_isPrimitiveForm_of_dvd_of_not_sq_dvd_of_not_dvd_conductor`](thm.html#GaloisRepAdic.charpoly_eq_of_isFrobeniusAt_of_isPrimitiveForm_of_dvd_of_not_sq_dvd_of_not_dvd_conductor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] O] (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (M₀ q : ℕ) (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀) (hqp : q ≠ p)
    (ε : DirichletCharacter ℂ (M₀ * q)) (hqε : ¬ q ∣ ε.conductor) (S : Finset ℕ)
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O)
    (e : ℕ → R)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M₀ * q → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod (M₀ * q)))
    (ρ : GaloisRepAdic O)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M₀ * q → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.det (ρ.ρ τ) = φ (e ℓ) * (ℓ : O))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : P.IsFrobeniusAt τ q)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M₀ * q) (hℓS : ℓ ∉ S) (hℓq : ℓ ≡ q [MOD M₀]) :
    LinearMap.det (ρ.ρ τ) = φ (e ℓ) * (q : O) := by sorry
