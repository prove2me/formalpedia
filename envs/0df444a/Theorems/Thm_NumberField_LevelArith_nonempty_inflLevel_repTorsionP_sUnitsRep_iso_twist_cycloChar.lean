-- Prove2me | Theorems.Thm_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
-- name    : NumberField.LevelArith.nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/82b7be55-757c-5cac-a35e-f55ad0a569b1
-- title:
--   p-torsion of the S-units is 𝔽ₚ(χ)
-- statement:
--   Let $p$ be a prime, $S$ a finite set of rational primes, and let $K \le L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, both finite-dimensional over $\mathbb{Q}$; write $L' =$ `levelField K L hKL` for $L$ regarded, via extension of scalars, as an intermediate field of $\overline{\mathbb{Q}}/K$, and assume $L'/K$ is normal. Let $\zeta \in \overline{\mathbb{Q}}$ be a primitive $p$-th root of unity with $\zeta \in L$. The conclusion asserts that a certain type of isomorphisms is nonempty, namely that the following two representations of the subgroup $K.\mathrm{fixingSubgroup} \le \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$ are isomorphic. The first is obtained from the $\mathbb{Z}$-linear representation of $\mathrm{Gal}(L'/K)$ on the $S_K$-units of $L'$ — the submodule of $\mathrm{Additive}\,(L')^{\times}$ cut out by `sUnits`, for $S_K$ the finite set of height-one primes of $\mathcal{O}_K$ lying over the primes in $S$ — by passing to the submodule killed by $p$, viewed as a $\mathbb{Z}/p$-representation (`repTorsionP`), and then restricting along `levelGal`, the map sending an element of $K.\mathrm{fixingSubgroup}$ to the corresponding automorphism of $\overline{\mathbb{Q}}$ over $K$ and restricting it to $L'$. The second is the rank-one representation on $\mathbb{Z}/p$ in which $g$ acts by multiplication by $\chi(g)$, where $\chi$ is the mod $p$ cyclotomic character `cycloChar p` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ composed with the inclusion of $K.\mathrm{fixingSubgroup}$.
--
--   This identifies the $p$-torsion of the $S$-unit group of $L'$ with the group $\mu_p$ of $p$-th roots of unity, on which the Galois group acts through the mod $p$ cyclotomic character; the hypothesis $\zeta \in L$ guarantees that this torsion is of order exactly $p$. It feeds the mod $p$ equivariant Dirichlet–Herbrand computation of $S$-unit invariants, [`NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq`](thm.html#NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq), where the torsion contribution to the $S$-unit module modulo $p$ must be recognised as $\mathbb{F}_p(\chi)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.LevelArith.nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L) :
    Nonempty (inflLevel K L hKL (repTorsionP p
        (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S))) ≅
      (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp K.fixingSubgroup.subtype)) := by sorry
