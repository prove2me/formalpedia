-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaC_residueField_eq_add_one
-- name    : ModularCurve.finrankAlong_heckeAlphaC_residueField_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/a5be39fb-806d-53c1-8cb0-2a51e284ad87
-- title:
--   Degeneracy embedding of level N into level Nℓ has degree ℓ+1
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (the Mathlib algebraic closure of $\mathbb{Q}$) which `LiesOverPrime q`, i.e. the image of $q$ lies in the nonunits of $A$, and write $k = \operatorname{ResidueField} A$ for its residue field. Let $\ell$ be a prime with $\ell \neq q$ and $\ell \nmid N$. Inside the field of Laurent series $k((X))$ consider the intermediate field $\mathtt{modularFunctionFieldC}\,k\,N$, generated over $k$ by the two series $\mathtt{jqModC}\,k$ and $\mathtt{jqNModC}\,k\,N$, and the larger intermediate field $\mathtt{charLDegeneracyRoof}\,k\,N\,\ell$, generated over $k$ by $\mathtt{jqModC}\,k$, $\mathtt{jqNModC}\,k\,N$, $\mathtt{jqNModC}\,k\,\ell$ and $\mathtt{jqNModC}\,k\,(N\ell)$. The map `heckeAlphaC` is the inclusion $k$-algebra homomorphism of the former into the latter. The assertion is that the degree of the roof as a module over $\mathtt{modularFunctionFieldC}\,k\,N$, via the algebra structure induced by that inclusion (`finrankAlong`), equals $\ell + 1$.
--
--   This is the degree of the first degeneracy embedding from level $N$ to level $N\ell$, in the characteristic-$q$ reduction of the modular function fields; classically it is the index $[\Gamma_0(N):\Gamma_0(N\ell)] = \psi(N\ell)/\psi(N) = \ell+1$ for a prime $\ell\nmid N$. It feeds the construction of Hecke correspondences and their transport in the Cerednik–Drinfeld and place-specialisation parts of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaC_residueField_eq_add_one.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsLocalRing ModularCurve
open AlgebraicCurve

theorem ModularCurve.finrankAlong_heckeAlphaC_residueField_eq_add_one
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓN : ¬ ℓ ∣ N) :
    finrankAlong (ResidueField A) (heckeAlphaC (ResidueField A) N ℓ) = ℓ + 1 := by sorry
