-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one
-- name    : ModularCurve.FullLevel.SemistableCovering.inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/146d27a9-87f9-5b49-835a-68d42e17e904
-- title:
--   Tame-character-one inertia induces the identity on a Drinfeld chart
-- statement:
--   Fix a prime $q$, a non-zero natural number $M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with residue field $\kappa = \mathrm{ResidueField}\,A$, and a finite set $W$ of places of $\kappa$ in `modularFunctionFieldC κ M'`. Let $\mathcal{C}$ be a `SemistableCovering q M' A W`, suppose $\kappa$ is an algebra over the field `GaloisField q 2` with `CoordRing q κ` a domain, and let $\pi \in \overline{\mathbb{Q}}$, let $\iota : \mathrm{GaloisField}(q,2) \to \kappa$ be a ring homomorphism, $\eta$ a natural number, $\zeta$ an element of `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$), and $s \in W$. Assume $\mathcal{C}$ satisfies `DrinfeldClause π ι η ζ s`, i.e. there are a subgroup $C$ of the $(q+1)$-st roots of unity of $\mathrm{GaloisField}(q,2)$ and an $\kappa$-isomorphism $e$ from $\mathcal{C}.\mathrm{FSS}\,s$ onto the corresponding fixed subfield [`DrinfeldCurve.quotField q κ C`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) of the Drinfeld function field, through which the $\Gamma_0(M')$-level automorphisms and the inertia automorphisms at $A$ act by the prescribed elements of `hSubgroup q`. Then for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with $A.\mathrm{tameCharacter}\,\pi\,\tau = 1$, the semilinear automorphism `arithmeticGalois` attached to $\tau$ on the base-changed function field `fieldBar q M'` preserves the integers of the chart $\mathcal{C}.\mathrm{CSS}\,s$ in both directions and induces on its residue field the identity automorphism.
--
--   This reads off the inertia part of the Drinfeld clause in the degenerate case of trivial tame character: inertia elements whose tame character is $1$ act trivially on the supersingular charts of the semistable model at full level $q^2M'$. It feeds the naturality statements for inertia on the supersingular components that transport discriminants through the tubes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup DrinfeldCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W)
    [Algebra (GaloisField q 2) (ResidueField A)] [IsDomain (CoordRing q (ResidueField A))]
    (π : AlgebraicClosure ℚ) (ι : GaloisField q 2 →+* ResidueField A) (η : ℕ) (ζ : Idx q) (s : ↥W)
    (hD : 𝒞.DrinfeldClause π ι η ζ s) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      SemistableCovering.InducesOnChart (𝒞.CSS s)
        (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) := by sorry
