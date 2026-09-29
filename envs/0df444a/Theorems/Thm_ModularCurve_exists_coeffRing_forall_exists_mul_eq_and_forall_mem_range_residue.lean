-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
-- name    : ModularCurve.exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c41549fa-0c93-5ff1-8972-4216673b2246
-- title:
--   Discrete valuation subring of a place capturing S and k₀
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ which lies over $p$ in the sense that the image of $p$ in $\overline{\mathbb Q}$ belongs to the non-units of $A$; assume further that the residue field of $A$ has characteristic $p$ and is algebraically closed. Let $\rho$ be a ring homomorphism from the coefficient ring `R p` (a subring of $\mathbb Q$, coerced into $\overline{\mathbb Q}$ by its structure map) into $A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is `algebraMap (R p) (AlgebraicClosure ℚ)`. Let $S$ be a finite subset of $\overline{\mathbb Q}$ and $k_0$ a finite subfield of the residue field of $A$. Then there exist a commutative ring $O'$ which is a domain and a discrete valuation ring, a homomorphism $\rho_{O'} \colon$ `R p` $\to O'$, an injective local homomorphism $\iota_{A'} \colon O' \to A$ with $\iota_{A'} \circ \rho_{O'} = \rho$, and a homomorphism $j_{O'} \colon O' \to \overline{\mathbb Q}$ which is $\iota_{A'}$ followed by the inclusion of $A$ and satisfies $j_{O'} \circ \rho_{O'} =$ `algebraMap (R p) (AlgebraicClosure ℚ)`, the two composites into the residue field of $A$ agreeing as well, such that every $c \in S$ is a quotient, i.e. there are $a, b \in O'$ with $j_{O'}(b) \neq 0$ and $c \, j_{O'}(b) = j_{O'}(a)$, and every element of $k_0$ lies in the image of the residue map composed with $\iota_{A'}$.
--
--   This is the standard construction of a coefficient ring inside a place of $\overline{\mathbb Q}$: the valuation ring of a suitable number field at the prime below $A$ is a discrete valuation ring whose fraction field contains a prescribed finite set of algebraic numbers and whose residue field contains a prescribed finite subfield of the residue field of $A$. It is used to supply the coefficient ring in [`ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq`](thm.html#ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (S : Finset (AlgebraicClosure ℚ)) (k₀ : Subfield (ResidueField ↥A)) [Finite ↥k₀] :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (ρO' : R p →+* O')
      (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA') (_ : ιA'.comp ρO' = ρ)
      (jO' : O' →+* AlgebraicClosure ℚ) (_ : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (_ : A.subtype.comp ιA' = jO')
      (_ : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ),
      (∀ c ∈ S, ∃ a b : O', jO' b ≠ 0 ∧ c * jO' b = jO' a) ∧
      (∀ ξ : ResidueField ↥A, ξ ∈ k₀ → ξ ∈ Set.range ((IsLocalRing.residue ↥A).comp ιA')) := by sorry
