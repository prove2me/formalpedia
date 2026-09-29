-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_injective_crossingPt_of_exists_section
-- name    : ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/df7e6197-f715-58d8-941c-eb3fdeecda62
-- title:
--   Injectivity of crossing points under residue-field rationality
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak X$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for level $\Gamma_0(N_0q)$ over the base ring `DRLevel.R q`. Let $O$ be a commutative local ring, $\rho_O \colon \mathrm{R}\,q \to O$ a ring homomorphism, and let $\kappa$ be an algebraically closed field of characteristic $q$ together with a ring homomorphism $\mathrm{to}\kappa \colon O \to \kappa$. Write $\mathcal C_0$ and $\mathcal C_1$ for the two component morphisms $\mathfrak X.\mathrm{comp}\ \kappa\ (\mathrm{to}\kappa \circ \rho_O)\ 0$ and $\ldots 1$ of the package into the geometric fibre `DRLevel.fibre (toκ.comp ρO)`, and for a point $n$ of the scheme-theoretic fibre product of $\mathcal C_0$ and $\mathcal C_1$ let $\mathfrak X.\mathrm{crossingPt}\ \rho_O\ \mathrm{to}\kappa\ n$ be the image of $n$ in the topological space of `DRLevel.XO ρO` under the first projection followed by $\mathcal C_0$ followed by the base-change morphism `DRLevel.bcMap ρO toκ` (the map of pullbacks induced by $\mathrm{Spec}$ of $\mathrm{to}\kappa$). Assume the rationality hypothesis `hrat`: for every such $n$ there is a morphism $s \colon \mathrm{Spec}\,(\mathrm{ResidueField}\,O) \to$ `DRLevel.fibre ((residue O).comp ρO)` which is a section of the second projection, i.e. $s$ followed by `pullback.snd` is the identity, and such that $\mathfrak X.\mathrm{crossingPt}\ \rho_O\ \mathrm{to}\kappa\ n$ equals the image under `DRLevel.bcMap ρO (IsLocalRing.residue O)` of the image under $s$ of the closed point of $\mathrm{Spec}\,(\mathrm{ResidueField}\,O)$. Then the map $n \mapsto \mathfrak X.\mathrm{crossingPt}\ \rho_O\ \mathrm{to}\kappa\ n$ is injective.
--
--   This is the node-separation step for the Deligne–Rapoport model at level $\Gamma_0(N_0q)$: the crossing points of the two components of the geometric fibre over $q$ remain distinct when read in the model over $O$, provided each of them comes from a point rational over the residue field of $O$. It supplies the injectivity input to the construction of a resolved model package, [`ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_and_dRResolvedModelChartsLevelRam`](thm.html#ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_and_dRResolvedModelChartsLevelRam).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_injective_crossingPt_of_exists_section.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (hrat : ∀ n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        𝔛.crossingPt ρO toκ n =
          (DRLevel.bcMap ρO (IsLocalRing.residue O)).base (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))) :
    Function.Injective fun n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)) => 𝔛.crossingPt ρO toκ n := by sorry
