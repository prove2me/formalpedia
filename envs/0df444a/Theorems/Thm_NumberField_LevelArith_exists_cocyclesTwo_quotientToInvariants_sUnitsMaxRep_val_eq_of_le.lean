-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le
-- name    : NumberField.LevelArith.exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/9f011c49-5064-5f50-b5db-0ad1556440b3
-- title:
--   Restricting an S-unit 2-cocycle to a larger base field
-- statement:
--   Let $S$ be a finite set of rational primes and let $L \le L' \le F$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, with $F$ finite-dimensional and normal over $\mathbb{Q}$. For an intermediate field $M$ write $\Gamma_M = M.\mathrm{fixingSubgroup}$, and let `sUnitsMaxRep S M` be the $\mathbb{Z}$-representation of $\Gamma_M$ on the additive group of the subgroup `sUnitsMaxStable S M` of $\overline{\mathbb{Q}}^\times$, regarded as a $\mathbb{Z}$-submodule of `Additive (AlgebraicClosure ℚ)ˣ` with the action coming from the Galois action on units; `sUnitsMaxRep.val` sends an element of this representation to the corresponding unit. Put $U_M = \Gamma_F \cap \Gamma_M$, realised as the preimage of $\Gamma_F$ under the inclusion of $\Gamma_M$, so that $\Gamma_M/U_M$ plays the role of $\mathrm{Gal}(F/M)$, and let $\Gamma_M/U_M$ act on the $U_M$-invariants of `sUnitsMaxRep S M`. Given a $2$-cocycle $f$ of $\Gamma_L/U_L$ with values in that invariant module, the assertion is that there exists a $2$-cocycle $f'$ of $\Gamma_{L'}/U_{L'}$ with values in the $U_{L'}$-invariants of `sUnitsMaxRep S L'` such that for all $g,h \in \Gamma_{L'}$ and all $g_0,h_0 \in \Gamma_L$ whose underlying $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ satisfy $g_0 = g$ and $h_0 = h$, the units $f'(\bar g,\bar h)$ and $f(\bar g_0,\bar h_0)$ have the same value in $\overline{\mathbb{Q}}$.
--
--   This is the restriction (along the inclusion $\Gamma_{L'} \subseteq \Gamma_L$) of a finite-layer $2$-cocycle with $S$-unit coefficients from the base $L$ to the larger base $L'$, with the matching of values recorded pointwise on underlying units rather than through an identification of coefficient modules. It feeds the descent step [`NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_map_principalIdele_eq_zero_of_pow_smul_eq_zero`](thm.html#NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_map_principalIdele_eq_zero_of_pow_smul_eq_zero) in the treatment of the layerwise Hasse principle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le
    (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f' : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)),
      ∀ (g h : ↥L'.fixingSubgroup) (g₀ h₀ : ↥L.fixingSubgroup),
      ((g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((h₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((sUnitsMaxRep.val S L' ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L ((f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by sorry
