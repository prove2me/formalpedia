-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep
-- name    : NumberField.LevelArith.exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d6c8cf3e-204b-595d-85e4-bdd61a6d2cfd
-- title:
--   Presenting a level-constant cochain at a finite Galois level
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes containing $p$, and an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ that is finite over $\mathbb Q$ and unramified outside $S$, in the sense that for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup $\Gamma_L$ of $L$. Let $n\in\mathbb N$ and let $u$ be an arbitrary function from $\Gamma_L^{\,n}$ to the $\mathbb Z$-linear representation `sUnitsMaxRep S L` of $\Gamma_L$ on (the additive group of) the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L` of $\overline{\mathbb Q}^\times$. Assume $u$ is level-constant: there is an intermediate field $F_0$, finite over $\mathbb Q$ and unramified outside $S$, such that $u(g\cdot s)=u(g)$ whenever every component of $s$ fixes $F_0$ pointwise. Let $F_1\supseteq L$ be a further intermediate field, finite over $\mathbb Q$ and unramified outside $S$. Then there is an intermediate field $F$ with $L\le F$, $F_1\le F$, finite over $\mathbb Q$, normal over $\mathbb Q$, unramified outside $S$, such that $F$ viewed over $L$ (the field `levelField L F`) is Galois over $L$, together with a function $f$ from $n$-tuples of cosets of $U_F:=\Gamma_F\cap\Gamma_L$ in $\Gamma_L$ to the $U_F$-invariants of `sUnitsMaxRep S L` (as a representation of $\Gamma_L/U_F$), with $u(g)=f(\bar g)$ for all $g\in\Gamma_L^{\,n}$, where $\bar g$ is the tuple of cosets of the components of $g$.
--
--   This is the statement that a level-constant inhomogeneous $n$-cochain of $\Gamma_L$ with values in the maximal $S$-units is the inflation of a cochain of a finite quotient $\Gamma_L/U_F$ with values in the $U_F$-invariants, with $F$ arranged to be normal over $\mathbb Q$, unramified outside $S$ and above a prescribed level $F_1$. It is used in the descent to finite levels in [`groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax`](thm.html#groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (n : ℕ) (u : (Fin n → ↥L.fixingSubgroup) → sUnitsMaxRep S L)
    (hlc : (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧
        ∀ g s : Fin n → ↥L.fixingSubgroup,
          (∀ i, ((s i : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F₀.fixingSubgroup) → u (g * s) = u g))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF₁ : L ≤ F₁) [FiniteDimensional ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : F₁ ≤ F) (_ : FiniteDimensional ℚ ↥F) (_ : Normal ℚ ↥F)
      (_ : IsGalois ↥L ↥(levelField L F hLF)) (_ : F.IsUnramifiedOutside S)
      (f : (Fin n → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin n → ↥L.fixingSubgroup, u g = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by sorry
