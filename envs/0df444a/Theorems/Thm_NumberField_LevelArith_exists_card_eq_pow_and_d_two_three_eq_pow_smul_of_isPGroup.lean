-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup
-- name    : NumberField.LevelArith.exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/aea1a9e4-a9cd-52b4-864f-613a1db43863
-- title:
--   Layer order p^k kills degree-3 cocycles at cochain level
-- statement:
--   Let $p$ be a prime, $S$ a finite set of rational primes, and $L$, $F$ intermediate fields of $\overline{\mathbb Q}/\mathbb Q$ with $F/\mathbb Q$ finite and normal. Write $\Gamma_L$ for the fixing subgroup of $L$ in $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ and $U_F$ for the preimage of the fixing subgroup of $F$ under the inclusion $\Gamma_L \hookrightarrow \mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$, so that $U_F = \Gamma_F \cap \Gamma_L$, and put $G = \Gamma_L/U_F$. Assume $G$ is a $p$-group. Let $M$ be the $\Gamma_L$-representation over $\mathbb Z$ obtained from the multiplicative action of $\Gamma_L$ on $\overline{\mathbb Q}^\times$ by restricting it to the $\mathbb Z$-submodule of $\mathrm{Additive}\,\overline{\mathbb Q}^\times$ attached to the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L`, and let $M^{U_F}$ be the induced representation of $G$ on the $U_F$-invariants of $M$. Let $f\colon G^3 \to M^{U_F}$ be an inhomogeneous $3$-cochain killed by the differential $d^{3,4}$ of the inhomogeneous cochain complex of $M^{U_F}$, i.e. a $3$-cocycle. Then there exist $k \in \mathbb N$ and a $2$-cochain $b_0\colon G^2 \to M^{U_F}$ with $\mathrm{card}\,G = p^k$ and $d^{2,3} b_0 = (p^k) \cdot f$ in the group of $3$-cochains.
--
--   This is the statement that the order of a finite group annihilates its cohomology in positive degrees, here for the layer group $G = \mathrm{Gal}(F_L/L)$ acting on the maximal $S$-unit module of $L$, and in the explicit cochain-level form $d b_0 = p^k f$ rather than as a statement about cohomology classes. It supplies the torsion witness used by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup.lean

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

theorem NumberField.LevelArith.exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (f : ((Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0) :
    ∃ (k : ℕ) (b₀ : ((Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))),
      Nat.card (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) = p ^ k ∧ ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f := by sorry
