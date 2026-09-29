-- Prove2me | Theorems.Thm_IsPrimitiveRoot_exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField_of_prime
-- name    : IsPrimitiveRoot.exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/ab40055f-d91f-5968-bf7d-2275fdb4a361
-- title:
--   Cyclotomic discrete valuation ring below a primitive q-th root of unity
-- statement:
--   Let $q$ be a prime (supplied as a `Fact`), and let $R$ be a commutative ring in `Type` that is an integral domain of characteristic zero and local, whose residue field `IsLocalRing.ResidueField R` has characteristic $q$; let $\zeta \in R$ be a primitive $q$-th root of unity in the sense of `IsPrimitiveRoot`. The assertion is the existence of the following data: a type $A$ together with a commutative ring structure making it an integral domain and a discrete valuation ring whose residue field is finite; an element $\varpi \in A$ generating the maximal ideal, i.e. $\mathfrak m_A = (\varpi)$, so that $\varpi$ is a uniformiser; a unit $\varepsilon \in A$ with $$\varpi^{\,q-1} = \varepsilon \cdot q$$ in $A$ (the natural number $q$ being read in $A$); and a ring homomorphism $\iota : A \to R$ which is local (nonunits pull back to nonunits, equivalently $\iota^{-1}(\mathfrak m_R) = \mathfrak m_A$) and satisfies $\iota(\varpi) = 1 - \zeta$. No lower bound on $q$ is imposed, so the case $q = 2$ is included.
--
--   This packages the standard local cyclotomic arithmetic of $\mathbb Z[\zeta_q]$ localised at the unique prime $(1-\zeta_q)$ above $q$, where $(1-\zeta_q)^{q-1}$ differs from $q$ by a unit, transported into an arbitrary characteristic-zero local domain containing a primitive $q$-th root of unity $\zeta$ via a local homomorphism sending the uniformiser to $1-\zeta$. It is used in the analysis of quotients by $(1-\zeta)$ and their adic completions in the full-level modular curve computations, specifically by [`ModularCurve.FullLevel.Diamond.isReduced_adicCompletion_quotient_span_one_sub_of_isPrimitiveRoot_of_nthSeries_eq_mul_X_pow_mul_levelModuliPackageAbs_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.isReduced_adicCompletion_quotient_span_one_sub_of_isPrimitiveRoot_of_nthSeries_eq_mul_X_pow_mul_levelModuliPackageAbs_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsPrimitiveRoot_exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField_of_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsPrimitiveRoot.exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField_of_prime
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    (hchar : CharP (IsLocalRing.ResidueField R) q)
    (ζ : R) (hζ : IsPrimitiveRoot ζ q) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Finite (IsLocalRing.ResidueField A))
      (ϖ : A) (_ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (ε : A) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : A))
      (ι : A →+* R) (_ : IsLocalHom ι), ι ϖ = 1 - ζ := by sorry
