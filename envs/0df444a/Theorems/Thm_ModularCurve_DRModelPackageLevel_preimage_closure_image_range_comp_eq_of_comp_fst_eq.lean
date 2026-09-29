-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_preimage_closure_image_range_comp_eq_of_comp_fst_eq
-- name    : ModularCurve.DRModelPackageLevel.preimage_closure_image_range_comp_eq_of_comp_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/ded84cb5-5eeb-59ee-a3a4-178dc7458e22
-- title:
--   Saturation of the geometric q-fibre components under morphisms over X
-- statement:
--   Fix an integer $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak X$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for level $(N_0,q)$, whose underlying total space carries the structure morphism `toBase N₀ q` to $\operatorname{Spec}$ of the base ring `DRLevel.R q`. Let $O$ be a commutative ring with a ring homomorphism $\rho_O \colon$ `DRLevel.R q` $\to O$, let $\kappa$ be an algebraically closed field of characteristic $q$, and let $\mathrm{to}\kappa \colon O \to \kappa$ be a ring homomorphism. Write $\mathfrak X_\kappa =$ `DRLevel.fibre (toκ.comp ρO)` for the fibre product of `toBase N₀ q` with $\operatorname{Spec}$ of the composite $\mathrm{to}\kappa \circ \rho_O$, and let `DRLevel.XO ρO` be the scheme associated with $\rho_O$, equipped like $\mathfrak X_\kappa$ with a first projection to the total space of the model. Let $\mathrm{bc} \colon \mathfrak X_\kappa \to$ `DRLevel.XO ρO` be any morphism of schemes such that $\mathrm{bc}$ followed by the first projection equals the first projection, and let $i \in \{0,1\}$. Then, for the underlying continuous map of $\mathrm{bc}$ and the set-theoretic range $C_i$ of the underlying map of the morphism `𝔛.comp κ (toκ.comp ρO) i` supplied by the package, $$\mathrm{bc}^{-1}\bigl(\overline{\mathrm{bc}(C_i)}\bigr) = C_i,$$ the closure being taken in the topological space of `DRLevel.XO ρO`.
--
--   For $q \nmid N_0$ the geometric fibre at $q$ of the Deligne–Rapoport model of $X_0(N_0q)$ is a union of two components, each a copy of the level-$N_0$ curve; the statement asserts that each of these two components is saturated, i.e. is the full preimage of a closed subset of the $O$-scheme, under any morphism compatible with the projections to the model. It is used in the identification of the maximal ideals of the model along the $q$-fibre ([`ModularCurve.DRModelPackageLevel.exists_maximalIdeal_eq_branchIdeal_sup_span_singleton`](thm.html#ModularCurve.DRModelPackageLevel.exists_maximalIdeal_eq_branchIdeal_sup_span_singleton)) and in [`V3AsmLevel.strict_iso`](thm.html#V3AsmLevel.strict_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_preimage_closure_image_range_comp_eq_of_comp_fst_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.preimage_closure_image_range_comp_eq_of_comp_fst_eq
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (bc : DRLevel.fibre (N₀ := N₀) (toκ.comp ρO) ⟶ DRLevel.XO (N₀ := N₀) ρO)
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _) (i : Fin 2) :
    bc.base ⁻¹' closure (bc.base '' Set.range (𝔛.comp κ (toκ.comp ρO) i).base) = Set.range (𝔛.comp κ (toκ.comp ρO) i).base := by sorry
