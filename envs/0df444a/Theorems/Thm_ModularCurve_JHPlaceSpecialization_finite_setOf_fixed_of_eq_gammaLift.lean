-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
-- name    : ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/8366b4b2-279c-576e-a874-8bea4526170d
-- title:
--   Finiteness of the diamond–Frobenius fixed locus on places
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$ (so $M/p$ is nonzero), and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime p`, i.e. $p$ lies in the nonunits of $A$, and assume its residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Put $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$, whose places are the valuation subrings of $\bar F$ that contain the image of $\kappa$, are proper and have principal ideal structure. Let $\bar p \in (\mathbb{Z}/(M/p))^\times$ be a unit whose underlying residue class is $p$, and let $\delta$ be any self-map of the set of places of $\bar F$ over $\kappa$ which acts as the semilinear automorphism attached, via `SemilinearAut.ofAlgAut`, to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)` — the level-$M/p$ diamond operator for the image subgroup $H' =$ `infSubgroup p M H hpM` of $H$ under reduction, evaluated at a chosen lift of $\bar p$ to $\Gamma_0(M/p)$. Then the set of places $v$ with $\varphi(\delta(\varphi\, v)) = v$, where $\varphi =$ `qExpFrobeniusPlaceModL κ Γ′ p` is the mod-$p$ Frobenius operator on places, is finite.
--
--   This is the finiteness of the collision locus of Frobenius twisted by the diamond $\langle \bar p\rangle$ on the places of the characteristic-$p$ fibre function field: such places are fixed by an iterate of Frobenius, hence are rational over a finite subfield, and so form a finite set. It is used in the construction of families of places of the $\Gamma_H$ specialisation data avoiding prescribed inertia behaviour, and in the differential-form model at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ModularCurve
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v) :
    {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) |
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite := by sorry
