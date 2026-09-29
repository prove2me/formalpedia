-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_isLevelConstant_d_two_three_eq_of_level_coboundary_sUnitsMaxRep
-- name    : NumberField.LevelArith.exists_isLevelConstant_d_two_three_eq_of_level_coboundary_sUnitsMaxRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/06180db6-770c-5e2d-8c66-745dc0fa4755
-- title:
--   Inflating a layer coboundary to a level-constant 2-cochain
-- statement:
--   Fix a finite set $S$ of rational primes and intermediate fields $L,F,F'$ of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, with $F$ and $F'$ normal over $\mathbb{Q}$, and assume $F'$ satisfies `IsUnramifiedOutside S`: $F'$ is finite-dimensional over $\mathbb{Q}$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of $F'$. Write $\Gamma_L$ for `L.fixingSubgroup`, $M =$ `sUnitsMaxRep S L` for its $\mathbb{Z}$-representation on the stable $S$-units submodule of $\overline{\mathbb{Q}}^{\times}$ (written additively), and $U_F$, $U_{F'}$ for the preimages in $\Gamma_L$ of the fixing subgroups of $F$, $F'$. Given a function $u : \Gamma_L^{3} \to M$, a function $f$ on $(\Gamma_L/U_F)^{3}$ with values in $M^{U_F}$ such that $u$ is the inflation of $f$, and a function $b$ on $(\Gamma_L/U_{F'})^{2}$ with values in $M^{U_{F'}}$ such that for every $g \in \Gamma_L^{3}$ the inflation of $f$ at $g$ equals the value at the image of $g$ of the inhomogeneous-cochain differential $d^{2,3}b$, the conclusion asserts the existence of $w : \Gamma_L^{2} \to M$ together with an intermediate field $F_0$ unramified outside $S$ in the above sense such that $w(g \cdot s) = w(g)$ whenever every component of $s$ lies in the fixing subgroup of $F_0$, and such that $d^{2,3}w = u$.
--
--   This is the step that converts a coboundary relation established on a finite layer $\Gamma_L/U_{F'}$ into a coboundary relation for cochains of $\Gamma_L$ itself, with the primitive kept constant on an open subgroup cut out by a field unramified outside $S$. It is the final assembly step used by [`groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax`](thm.html#groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_isLevelConstant_d_two_three_eq_of_level_coboundary_sUnitsMaxRep.lean

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

theorem NumberField.LevelArith.exists_isLevelConstant_d_two_three_eq_of_level_coboundary_sUnitsMaxRep
    (S : Finset Nat.Primes) (L F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] [Normal ℚ ↥F'] (hF' : F'.IsUnramifiedOutside S)
    (u : (Fin 3 → ↥L.fixingSubgroup) → sUnitsMaxRep S L)
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hu : ∀ g : Fin 3 → ↥L.fixingSubgroup, u g = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L))
    (b : (Fin 2 → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hb : ∀ g : Fin 3 → ↥L.fixingSubgroup,
      ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
        = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) :
    ∃ w : (Fin 2 → ↥L.fixingSubgroup) → sUnitsMaxRep S L,
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → ↥L.fixingSubgroup,
          (∀ i, ((s i : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F₀.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains (sUnitsMaxRep S L)).d 2 3).hom w = u := by sorry
