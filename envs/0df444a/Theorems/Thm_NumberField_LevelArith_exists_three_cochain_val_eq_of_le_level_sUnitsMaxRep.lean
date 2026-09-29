-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep
-- name    : NumberField.LevelArith.exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/052ced21-4f28-57b1-b57e-3f884c06975d
-- title:
--   Inflation of degree-3 cochain data to a larger layer
-- statement:
--   Fix a natural number $p$, a finite set $S$ of rational primes and intermediate fields $L, F, F_1$ of $\overline{\mathbb Q}/\mathbb Q$ with $F \le F_1$, both $F$ and $F_1$ finite over $\mathbb Q$ and normal over $\mathbb Q$. Write $\Gamma_L$ for the fixing subgroup of $L$ and, for a field $E$, write $U_E = \Gamma_E \cap \Gamma_L$ for the preimage in $\Gamma_L$ of the fixing subgroup of $E$; let $M =$ `sUnitsMaxRep S L` be the $\mathbb Z[\Gamma_L]$-module obtained from the submodule `sUnitsMaxSubmodule S L` of $\mathrm{Additive}\,(\overline{\mathbb Q})^{\times}$ cut out by the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L`, with the action induced by multiplication of units. For an open-type subgroup $U \le \Gamma_L$ let $M^{U}$ denote `quotientToInvariants`, the $U$-invariants of $M$ regarded as a representation of $\Gamma_L/U$. Suppose given an inhomogeneous $3$-cochain $f \colon (\Gamma_L/U_F)^3 \to M^{U_F}$, an integer $k \ge 0$ and a $2$-cochain $b_0$ with $d^{2,3} b_0 = p^k \cdot f$. Then there exist a $3$-cochain $f_1 \colon (\Gamma_L/U_{F_1})^3 \to M^{U_{F_1}}$ and a $2$-cochain $b_{0,1}$ such that: $d^{3,4} f = 0$ implies $d^{3,4} f_1 = 0$; $d^{2,3} b_{0,1} = p^k \cdot f_1$; and for every $g \colon \mathrm{Fin}\,3 \to \Gamma_L$ the value of $f_1$ at the classes of $g$ modulo $U_{F_1}$ coincides, as an element of $M$, with the value of $f$ at the classes of $g$ modulo $U_F$.
--
--   This is the inflation step for cochain-level data attached to the maximal $S$-unit module over $L$: it transports a degree-$3$ cochain together with a witness that $p^k$ times it is a coboundary from the layer cut out by $F$ to the layer cut out by a larger field $F_1$, without changing the values of the cochain on $\Gamma_L$-tuples. It is used in [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup), where such data must be compared across layers of a tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep.lean

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

theorem NumberField.LevelArith.exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep
    {p : ℕ} (S : Finset Nat.Primes) (L F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [FiniteDimensional ℚ ↥F₁] [Normal ℚ ↥F₁]
    (f : ((Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (k : ℕ) (b₀ : ((Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) :
    ∃ (f₁ : ((Fin 3 → (↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)))) (b₀₁ : ((Fin 2 → (↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)))),
      (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0 → ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f₁ = 0) ∧
      ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀₁ = (p ^ k : ℤ) • f₁ ∧
      (∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f₁ (fun i => (g i : (↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) := by sorry
