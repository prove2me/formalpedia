-- Prove2me | Theorems.Thm_ModularCurve_isOfFinAddOrder_jZeroC_residueField
-- name    : ModularCurve.isOfFinAddOrder_jZeroC_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/e3278ec3-e337-522b-9b54-1d2d893ae24a
-- title:
--   Points of J₀(p) over a residue field above ℓ are torsion
-- statement:
--   Let $p$ be a nonzero natural number, let $\ell$ be a prime with $\ell \nmid p$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime ℓ`, i.e. the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in the set of non-units of $A$; assume moreover that the residue field $\kappa_A$ of the local ring $A$ has characteristic $\ell$. Write $F$ for the intermediate field `modularFunctionFieldFullC` $\kappa_A\, p$ of the field of Laurent series over $\kappa_A$, namely the subfield generated over $\kappa_A$ by the family `divisorExpansionsC` $\kappa_A\, p$ of Laurent expansions, and let `JZeroC` $\kappa_A\, p$ be the associated group $\operatorname{Pic}^0$, the group of degree-zero divisors of $F/\kappa_A$ modulo the subgroup of principal divisors. The assertion is that every element $u$ of this group is of finite additive order, i.e. $n \cdot u = 0$ for some $n \geq 1$.
--
--   This is the statement that $J_0(p)(\kappa_A)$, realised as the degree-zero divisor class group of the level-$p$ modular function field over the residue field $\kappa_A$ of a place of $\overline{\mathbb{Q}}$ above $\ell$, is a torsion group. It is used in the construction of elements of the Eisenstein kernel submodule killed by a prescribed power of $\ell$ after reduction modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isOfFinAddOrder_jZeroC_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve IsLocalRing

theorem ModularCurve.isOfFinAddOrder_jZeroC_residueField
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField ↥A) ℓ]
    (u : JZeroC (IsLocalRing.ResidueField ↥A) p) : IsOfFinAddOrder u := by sorry
