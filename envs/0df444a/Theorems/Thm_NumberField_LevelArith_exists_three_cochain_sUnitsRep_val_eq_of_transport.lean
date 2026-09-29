-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_three_cochain_sUnitsRep_val_eq_of_transport
-- name    : NumberField.LevelArith.exists_three_cochain_sUnitsRep_val_eq_of_transport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3cba0777-34c7-5b9e-b20d-9b4549e6b24c
-- title:
--   Transporting a degree-3 cochain to the S-units frame
-- statement:
--   Fix a finite set $S$ of rational primes and intermediate fields $L \le F$ of $\overline{\mathbb Q}/\mathbb Q$, both of finite degree over $\mathbb Q$, with $F/\mathbb Q$ normal, and write $F_L :=$ `levelField L F hLF` for $F$ viewed as an extension of $L$ inside $\overline{\mathbb Q}$, assumed Galois over $L$. Let $\Gamma_L := L^{\mathrm{fix}}$ and $U_F := F^{\mathrm{fix}} \cap \Gamma_L$ (the comap of $F$'s fixing subgroup along the inclusion of $\Gamma_L$). Let $\iota : \mathrm{Gal}(F_L/L) \to \Gamma_L/U_F$ be a group homomorphism with $\iota(\mathrm{levelGal}(g)) = \bar g$ for all $g \in \Gamma_L$, where `levelGal` restricts an element of $\Gamma_L$ to $F_L$. Let $\varphi$ be a morphism of $\mathbb Z$-representations of $\mathrm{Gal}(F_L/L)$ from the restriction along $\iota$ of the $U_F$-invariants of `sUnitsMaxRep S L` (a $\Gamma_L$-submodule of $\mathrm{Additive}\,\overline{\mathbb Q}^{\times}$) to `sUnitsRep` of $F_L$ for the finset of primes of $\mathcal O_L$ above $S$, with $\varphi$ bijective on underlying modules and value-preserving: the underlying element of $\overline{\mathbb Q}$ of $\varphi(x)$ equals that of $x$. Then for every function $f : (\mathrm{Fin}\,3 \to \Gamma_L/U_F) \to (E_S)^{U_F}$ there is $f_1 : (\mathrm{Fin}\,3 \to \mathrm{Gal}(F_L/L)) \to$ the $S$-units module such that the degree $3 \to 4$ inhomogeneous-cochain differential kills $f_1$ whenever it kills $f$, and for all $g : \mathrm{Fin}\,3 \to \Gamma_L$ one has $f_1(\mathrm{levelGal}\,g_i) = f(\bar g_i)$ as elements of $\overline{\mathbb Q}$.
--
--   This is the transport step that moves a degree-$3$ inhomogeneous cochain of $\Gamma_L/U_F$ with values in the $U_F$-invariants of the stable $S$-units of $\overline{\mathbb Q}$ to a cochain of $\mathrm{Gal}(F_L/L)$ with values in the $S$-units of the layer $F_L$, preserving values in $\overline{\mathbb Q}$ and the cocycle condition. It serves the $p$-group arguments about degree-$3$ cochain identities at a finite level, being used by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup) and [`NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_three_cochain_sUnitsRep_val_eq_of_transport.lean

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
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_three_cochain_sUnitsRep_val_eq_of_transport
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0 → ((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 3 4).hom f₁ = 0) ∧
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by sorry
