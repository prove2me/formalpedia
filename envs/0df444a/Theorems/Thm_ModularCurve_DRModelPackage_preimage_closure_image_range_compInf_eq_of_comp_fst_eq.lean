-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq
-- name    : ModularCurve.DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/0b39e8c2-8869-5c77-9021-26103a62320b
-- title:
--   Saturation of the two geometric p-fibre components under X-morphisms
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a term of `DRModelPackage p`, the bundled datum consisting of the two-chart integral model `DRModel p` of the modular curve — the pushout of the two affine charts of the function field `modularFunctionFieldFull p` with respect to the Igusa parameter, with structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb Z$ — together with its properness, flatness, integrality and normality on affine opens, its generic-fibre curve models over $\mathbb Q$ and over $\overline{\mathbb Q}$ with the Galois- and place-compatibilities, the two sections `εinf`, `εzero`, the distinguished open `smoothLocus`, and the component morphisms `compInf`, `compZero`. Let $O$ be any commutative ring and let $\kappa$ be an algebraically closed field of characteristic $p$. Write $\mathfrak X_\kappa$ and $\mathfrak X_O$ for the pullbacks of `DRModel.toBase p` along $\operatorname{Spec}\kappa\to\operatorname{Spec}\mathbb Z$ and $\operatorname{Spec} O\to\operatorname{Spec}\mathbb Z$, and let $\mathrm{bc}\colon \mathfrak X_\kappa\to\mathfrak X_O$ be a morphism of schemes such that $\mathrm{bc}$ followed by the first projection $\mathfrak X_O\to$ `DRModel p` equals the first projection $\mathfrak X_\kappa\to$ `DRModel p`. Then, on underlying topological spaces, the preimage under $\mathrm{bc}$ of the closure of the image of the range of the map induced by `𝔛.compInf κ` equals that range, and likewise with `𝔛.compZero κ` in place of `𝔛.compInf κ`.
--
--   The two morphisms `compInf` and `compZero` carry the two components of the geometric fibre of the Deligne–Rapoport model at $p$; the assertion is that each of these closed subsets of $\mathfrak X_\kappa$ is saturated for any morphism to a base change over an arbitrary coefficient ring $O$ that is compatible with the projections to `DRModel p`, no compatibility over the bases and no hypotheses on $O$ being needed. It is used in the computation of the residue fields and local rings along the two components, notably in the identification of the maximal ideal at a crossing point as a branch ideal together with $p$, and in the construction of the ring maps from the function field to the residue fields at the generic points of the two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _) :
    bc.base ⁻¹' closure (bc.base '' Set.range (𝔛.compInf κ).base) = Set.range (𝔛.compInf κ).base ∧
    bc.base ⁻¹' closure (bc.base '' Set.range (𝔛.compZero κ).base) = Set.range (𝔛.compZero κ).base := by sorry
