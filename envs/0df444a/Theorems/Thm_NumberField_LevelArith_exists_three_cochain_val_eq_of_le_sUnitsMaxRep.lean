-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_sUnitsMaxRep
-- name    : NumberField.LevelArith.exists_three_cochain_val_eq_of_le_sUnitsMaxRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/60132dd1-72c2-50d1-94f4-35112c1fb331
-- title:
--   Restriction of degree-3 S-unit cochain data to a larger base
-- statement:
--   Fix a natural number $p$, a finite set $S$ of rational primes, and intermediate fields $L \le L' \le F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, with $F$ finite-dimensional and normal over $\mathbb{Q}$. For an intermediate field $M$ write $\Gamma_M =$ `M.fixingSubgroup` for its fixing subgroup in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$, $U_M = \Gamma_F \cap \Gamma_M$ for the preimage of $\Gamma_F$ in $\Gamma_M$, and let `sUnitsMaxRep S M` be the $\mathbb{Z}[\Gamma_M]$-module obtained from the multiplicative action of $\Gamma_M$ on $\overline{\mathbb{Q}}^{\times}$ restricted to the $\Gamma_M$-stable subgroup `sUnitsMaxStable S M`, written additively; `quotientToInvariants` passes to the $U_M$-invariants as a representation of $\Gamma_M/U_M$. Given an inhomogeneous $3$-cochain $f$ of $\Gamma_L/U_L$ with values in those invariants, a natural number $k$, and a $2$-cochain $b_0$ with $d^{2,3} b_0 = p^k \cdot f$, the conclusion produces a $3$-cochain $f'$ and a $2$-cochain $b_0'$ for $\Gamma_{L'}/U_{L'}$ with values in the corresponding invariants such that: $d^{3,4} f = 0$ implies $d^{3,4} f' = 0$; $d^{2,3} b_0' = p^k \cdot f'$; and for all $g : \mathrm{Fin}\,3 \to \Gamma_{L'}$ and $g_0 : \mathrm{Fin}\,3 \to \Gamma_L$ whose components agree as automorphisms of $\overline{\mathbb{Q}}$, the value of $f'$ at the classes of the $g(i)$ and the value of $f$ at the classes of the $g_0(i)$ have the same image in $\overline{\mathbb{Q}}$.
--
--   This is restriction of inhomogeneous cochains along $\Gamma_{L'}/U_{L'} \to \Gamma_L/U_L$ for the maximal $S$-unit coefficient module, carrying along a witness that $p^k$ times the cochain is a coboundary, with the pointwise identification of values recorded explicitly. It is the degree-$3$ instance of the layer-restriction step and is used in the descent to a $p$-Sylow subgroup in [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup) and in [`NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul`](thm.html#NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_sUnitsMaxRep.lean

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

theorem NumberField.LevelArith.exists_three_cochain_val_eq_of_le_sUnitsMaxRep
    {p : ℕ} (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (k : ℕ) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) :
    ∃ (f' : (Fin 3 → (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) (b₀' : (Fin 2 → (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))),
      (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0 → ((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d 3 4).hom f' = 0) ∧
      ((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d 2 3).hom b₀' = (p ^ k : ℤ) • f' ∧
      (∀ (g : Fin 3 → ↥L'.fixingSubgroup) (g₀ : Fin 3 → ↥L.fixingSubgroup),
        (∀ i, ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((g i : ↥L'.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
        ((sUnitsMaxRep.val S L' ((f' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g₀ i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) := by sorry
