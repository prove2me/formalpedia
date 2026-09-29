-- Prove2me | Theorems.Thm_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
-- name    : MonoidHom.exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/bd61c39d-39ac-5088-9f42-57fad2ef1d49
-- title:
--   Twisted mod p cyclotomic character: Frobenius and conjugation values
-- statement:
--   Let $k$ be a field of characteristic a prime $p$, let $M$ be a nonzero natural number and let $\chi\colon(\mathbb{Z}/M)^\times\to k^\times$ be a group homomorphism. Then there exists a homomorphism $\psi\colon\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to k^\times$, where $\overline{\mathbb{Q}}$ is the algebraic closure of $\mathbb{Q}$ and the Galois group is the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, with the following three properties. First, the kernel of $\psi$ is open as a subset of the Galois group. Second, $\psi(c)=-\chi(-1)$ in $k^\times$, where $c$ is [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30), the restriction to $\overline{\mathbb{Q}}$ of the star automorphism of $\mathbb{C}$ viewed as a $\mathbb{Q}$-algebra automorphism. Third, for every prime $\ell$ with $\ell\nmid M$ and $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma$ in the Galois group lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ by $x\mapsto x^{\ell}$, one has the identity $\psi(\sigma)=\ell\cdot\chi(\ell \bmod M)$ of elements of $k$, where $\ell \bmod M$ is the unit of $\mathbb{Z}/M$ determined by the coprimality of $\ell$ and $M$.
--
--   This produces the twist of the mod $p$ cyclotomic character by a Dirichlet-type character of $(\mathbb{Z}/M)^\times$, together with its values at Frobenius elements and at complex conjugation; it is the source of the auxiliary characters used to adjust determinants and odd/even behaviour of residual representations. It is cited in the analysis of absolutely irreducible residual Galois representations, in particular in the construction of primes with prescribed Frobenius trace and in the Eisenstein-type criterion for failure of absolute irreducibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul.lean

import Mathlib
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MonoidHom.exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (M : ℕ) [NeZero M] (χ : (ZMod M)ˣ →* kˣ) :
    ∃ ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ,
      IsOpen ((ψ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∧
      ψ complexConjugation = -χ (-1) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            (ψ σ : k) = (ℓ : k) *
              (χ (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)) : k) := by sorry
