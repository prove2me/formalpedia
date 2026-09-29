-- Prove2me | Theorems.Thm_IsLocalRing_not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit
-- name    : IsLocalRing.not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/510fbd0b-b3bd-5b88-bc08-3761ef41c310
-- title:
--   An element dividing a unit of 𝒪 is not residually zero
-- statement:
--   Let $\mathcal O$ be a commutative local ring and $F$ a nontrivial commutative $\mathcal O$-algebra. Let $x, y \in F$ with $y$ integral over $\mathcal O$, and let $u \in \mathcal O$ be a unit such that $x y$ equals the image of $u$ under the structure map $\mathcal O \to F$. The assertion is that there is no polynomial $R \in \mathcal O[X]$ which is monic, satisfies $R(x) = 0$ (evaluation via the algebra map, `Polynomial.aeval`), and whose image under the coefficientwise reduction by the residue map $\mathcal O \to \mathcal O/\mathfrak m$ equals $(X - C\,0)^{\deg R}$, i.e. $X^{\deg R}$ with $\deg R$ the `natDegree` of $R$. Existence of such an $R$ is the polynomial surrogate for the condition '$x$ reduces to $0$' in an $\mathcal O$-algebra carrying no residue map of its own; the theorem says that an element whose product with an integral element is a unit of $\mathcal O$ never satisfies it. Note that $x$ is not assumed integral over $\mathcal O$ separately: the hypothetical monic $R$ annihilating $x$ supplies that.
--
--   A local-algebra statement of Nakayama type: an element dividing a unit of the base local ring cannot be residually zero, phrased so as to apply in an algebraic closure of the fraction field of $\mathcal O$ where no residue homomorphism is available. It is used in the analysis of the roots of the local Hecke polynomials attached to a newform, in [`CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne`](thm.html#CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne), to rule out that a root dividing a unit reduces to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit.lean

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nakayama

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsLocalRing.not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {F : Type} [CommRing F] [Nontrivial F] [Algebra 𝒪 F]
    (x y : F) (hy : IsIntegral 𝒪 y) (u : 𝒪) (hu : IsUnit u)
    (hxy : x * y = algebraMap 𝒪 F u) :
    ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree) := by sorry
