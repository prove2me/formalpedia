-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq
-- name    : NumberField.LevelArith.exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d6640d9f-d41a-5893-915e-aa5e8bd58a59
-- title:
--   Cocycles with equal inflated class differ by a coboundary at a deeper level
-- statement:
--   Fix a finite set $S$ of rational primes and an intermediate field $L$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, finite over $\mathbb{Q}$, satisfying `IsUnramifiedOutside S`: for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of $L$. Let $F$ be a further intermediate field with $L \le F$, finite and normal over $\mathbb{Q}$ and again unramified outside $S$ in the same sense. Put $\Gamma_L =$ `L.fixingSubgroup`, let $U_F =$ `F.fixingSubgroup.comap L.fixingSubgroup.subtype` be its normal subgroup cut out by $F$, and let $E_S =$ `sUnitsMaxRep S L` be the $\mathbb{Z}[\Gamma_L]$-module obtained from the submodule `sUnitsMaxSubmodule S L` of $\mathrm{Additive}\,\overline{\mathbb{Q}}^{\times}$ attached to `sUnitsMaxStable S L`. Let $f_1, f_2$ be $2$-cocycles of $\Gamma_L/U_F$ valued in the representation $E_S^{U_F}$ (`quotientToInvariants`), and assume their classes have the same image under `continuousH2SrInflation`, the $\mathbb{Z}$-linear map from $H^2(\Gamma_L/U_F, E_S^{U_F})$ to `continuousH2Sr`, the quotient of $S$-level $2$-cocycles by $S$-level $2$-coboundaries. Then there exist an intermediate field $F'$ unramified outside $S$, Galois over $\mathbb{Q}$, with $F \le F'$, and a function $b$ from $\Gamma_L/U_{F'}$ to $E_S^{U_{F'}}$, such that for all $g, h \in \Gamma_L$ the difference $f_1(\bar g, \bar h) - f_2(\bar g, \bar h)$, computed inside $E_S$, equals the value at $(\bar g, \bar h)$ of the differential `d₁₂` of $b$ at level $F'$, again read inside $E_S$.
--
--   This is the two-cocycle form of the statement that the kernel of inflation from a finite layer into the continuous (Galois $S$-level) $H^2$ consists of classes that die at a deeper finite layer: two cocycles at the layer $F$ inflating to the same class in $H^2_S(\Gamma_L, E_S)$ become cohomologous, as cochains compared in $E_S$, after passing to some Galois layer $F' \supseteq F$ unramified outside $S$. It is used in the comparison of local invariants of $S$-level classes, in [`NumberField.LevelArith.eq_of_hasBrauerLocalInvAt`](thm.html#NumberField.LevelArith.eq_of_hasBrauerLocalInvAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
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

theorem NumberField.LevelArith.exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L] (hL : L.IsUnramifiedOutside S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (f₁ f₂ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hinfl : continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f₁)
        = continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f₂)) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g h : ↥L.fixingSubgroup,
        ((f₁ ((g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          - ((f₂ ((g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = (((d₁₂ ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).hom b ((g : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by sorry
