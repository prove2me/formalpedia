-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_comp_eq_of_le_sUnitsMaxRep
-- name    : NumberField.LevelArith.exists_level_comp_eq_of_le_sUnitsMaxRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c2455180-9823-52fb-b400-8fd69816ffb2
-- title:
--   Inflating a layer cochain to a larger layer
-- statement:
--   Fix a finite set $S$ of rational primes and three intermediate fields $L$, $F$, $F'$ of $\overline{\mathbb Q}/\mathbb Q$ (inside `AlgebraicClosure ℚ`), with $F$ and $F'$ normal over $\mathbb Q$ and $F \le F'$. Write $\Gamma_L =$ `L.fixingSubgroup` for the subgroup of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ fixing $L$ pointwise, and $U_F$, $U_{F'}$ for the preimages in $\Gamma_L$ of the fixing subgroups of $F$, $F'$ under the inclusion of $\Gamma_L$. Let $M =$ `sUnitsMaxRep S L` be the representation of $\Gamma_L$ on the $\mathbb Z$-module $\mathrm{Additive}\,(\overline{\mathbb Q})^\times$ cut out by the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L`, i.e. the subrepresentation of the multiplicative Galois action on units determined by that subgroup. Given $n : \mathbb N$ and an arbitrary function $f$ from $n$-tuples of cosets in $\Gamma_L/U_F$ to the $U_F$-invariants of $M$ (the submodule `quotientToInvariants`), the assertion is that there exists a function $f'$ from $n$-tuples of cosets in $\Gamma_L/U_{F'}$ to the $U_{F'}$-invariants of $M$ such that for every $g : \mathrm{Fin}\,n \to \Gamma_L$ the values $f'(\bar g)$ and $f(\bar g)$ agree as elements of $M$, where $\bar g$ denotes the componentwise image of $g$ in the respective quotient. No cocycle or continuity condition is imposed on $f$.
--
--   This is the set-theoretic inflation step used to pass from cochains at one finite layer of the tower to cochains at a larger layer, as is needed when realising continuous cochains with values in the $S$-units module as limits over finite quotients. It is cited in the construction of level-constant cochains in [`groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax`](thm.html#groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_comp_eq_of_le_sUnitsMaxRep.lean

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

theorem NumberField.LevelArith.exists_level_comp_eq_of_le_sUnitsMaxRep
    (S : Finset Nat.Primes) (L F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] [Normal ℚ ↥F'] (hFF' : F ≤ F')
    (n : ℕ) (f : (Fin n → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f' : (Fin n → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g : Fin n → ↥L.fixingSubgroup,
        ((f' (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by sorry
