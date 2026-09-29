-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
-- name    : ModularCurve.FullLevel.SemistableCovering.inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/09d189cd-93b4-51f2-a9f5-7ffa8114889e
-- title:
--   Tame inertia acts trivially on transported Igusa charts
-- statement:
--   Let $q$ be a prime, $M'$ a non-zero natural number, $A$ a valuation subring of $\overline{\mathbb{Q}}$, and $W$ a finite set of places of the modular function field $\mathrm{modularFunctionFieldC}$ of level $M'$ over the residue field of $A$. Assume $A$ lies over $q$, in the sense that $q$ is a non-unit of $A$, that $q \nmid M'$, and that $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$. Let $\mathcal{C}$ be a `SemistableCovering q M' A W`, let $\zeta$ be an index in `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and assume the component chart $\mathcal{C}.\mathrm{CIg}$ attached to the line $\infty = [1:0] \in \mathbb{P}^1(\mathbb{Z}/q)$ has Gauss presentation: an element $f$ of $F =$ `fieldBar q M'` (the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion field of level $q^2M'$ and subgroup $\mathrm{levelH}$, the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$) lies in that chart's valuation ring precisely when there are Laurent series $x,y$ over $A$ with $y$ having non-zero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ inside Laurent series over $\overline{\mathbb{Q}}$. Let $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$ and $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$ be such that the valuation ring of $\mathcal{C}.\mathrm{CIg}\,\ell$ is the preimage of that of $\mathcal{C}.\mathrm{CIg}\,\infty$ under the level automorphism `levelAutBar q M' ζ γ` of $F$ over $\overline{\mathbb{Q}}$. Finally let $\tau$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lying in the image of the inertia subgroup of $A$ inside its decomposition subgroup, with tame character value $A.\mathrm{tameCharacter}\,\pi\,\tau = 1$, i.e. the residue of $\tau\pi/\pi$ is $1$. Then the semilinear automorphism $g_\tau$ of $F$ obtained by applying $\tau$ to the coefficients of Laurent series induces the identity on the chart $\mathcal{C}.\mathrm{CIg}\,\ell$: for every $f \in F$ one has $f$ in the chart's valuation ring if and only if $g_\tau \cdot f$ is, and for every such $f$ the chart's residue map sends $g_\tau \cdot f$ and $f$ to the same element of the chart's residue field.
--
--   This is the Igusa-component half of the statement that the full-level semistable covering is defined over the tame extension: inertia elements of tame character value $1$ stabilise each Igusa chart and act trivially on its reduction. It feeds the inertia clause `inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs` of the semistable covering of the modular curve of level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (𝒞 : SemistableCovering q M' A W) (ζ : Idx q)
    (hO : ∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (ℓ : CuspidalType.ProjLine q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hℓ : (𝒞.CIg ℓ).integers = ((𝒞.CIg (lineInfty q)).integers).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) (hτπ : A.tameCharacter π τ = 1) :
    SemistableCovering.InducesOnChart (𝒞.CIg ℓ)
      (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) := by sorry
