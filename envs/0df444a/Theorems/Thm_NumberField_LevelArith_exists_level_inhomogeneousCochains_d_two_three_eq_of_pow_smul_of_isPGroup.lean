-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup
-- name    : NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/2f92c29a-5e78-5ca3-a877-fc23187fecf8
-- title:
--   Killing a degree-three S-unit cocycle at a deeper level
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$. Let $L\subseteq\overline{\mathbb{Q}}$ be a finite intermediate field of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ which is unramified outside $S$, meaning that $L$ is finite over $\mathbb{Q}$ and for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume moreover that $L$ contains a square root of $-1$ in case $p=2$. Let $F\supseteq L$ be a further intermediate field, finite over $\mathbb{Q}$, normal over $\mathbb{Q}$ and unramified outside $S$ in the same sense, and suppose the quotient $\Gamma_L/U_F$ of the fixing subgroup of $L$ by the preimage in it of the fixing subgroup of $F$ is a $p$-group. Let $f$ be an inhomogeneous $3$-cochain of $\Gamma_L/U_F$ with values in the $U_F$-invariants of the $\mathbb{Z}$-representation `sUnitsMaxRep S L` of $\Gamma_L$ on the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L` of $\overline{\mathbb{Q}}^\times$, written additively, and assume $f$ is a cocycle, i.e. its differential in degree $3$ vanishes. Assume also that $p^{k}\cdot f$ is the differential of a $2$-cochain $b_0$ for some $k\in\mathbb{N}$. Then there exist an intermediate field $F'$ which is unramified outside $S$, Galois over $\mathbb{Q}$ and contains $F$, and an inhomogeneous $2$-cochain $b$ of $\Gamma_L/U_{F'}$ with values in the $U_{F'}$-invariants of `sUnitsMaxRep S L`, such that for every triple $g:\mathrm{Fin}\,3\to\Gamma_L$ the value of $f$ at the classes of $g$ modulo $U_F$ and the value of the differential of $b$ at the classes of $g$ modulo $U_{F'}$ agree after inclusion of both invariant submodules into `sUnitsMaxRep S L`. The proof shown discards $k$, $b_0$ and the divisibility hypothesis.
--
--   This is the finite-layer form of the vanishing of the $p$-primary part of $H^3$ of the $S$-ramified Galois group acting on $S$-units: the inflation of the class of $f$ from level $F$ to a suitable deeper level $F'$ is zero. It feeds the corresponding statement without the $p$-group hypothesis on $\mathrm{Gal}(F/L)$, [`NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul`](thm.html#NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup.lean

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
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain
open NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0)
    (k : ℕ) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b : (Fin 2 → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by sorry
