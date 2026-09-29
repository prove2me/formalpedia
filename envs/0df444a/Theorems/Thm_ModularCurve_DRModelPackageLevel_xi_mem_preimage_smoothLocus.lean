-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_xi_mem_preimage_smoothLocus
-- name    : ModularCurve.DRModelPackageLevel.xi_mem_preimage_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/5c2ceffd-3deb-5084-9c08-f509a8dbe572
-- title:
--   The points ξ_∞ and ξ₀ lie over the smooth locus
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime with $q \nmid N_0$, and let $\mathfrak{X}$ be a level-$(N_0,q)$ Deligne–Rapoport model package of type `DRModelPackageLevel N₀ q hqN`: a structure carrying the curve `X N₀ q` together with the structure morphism `DRLevel.toBase N₀ q` to $\operatorname{Spec}(R_q)$ (the Igusa-type morphism for level $N_0 q$ at $q$), which is recorded as proper, flat and locally of finite presentation with integral source and integrally closed sections on affine opens, data identifying the geometric generic fibre with a smooth proper integral curve model over $\overline{\mathbb{Q}}$ compatibly with the Galois action and the chart coordinates, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbb{Q}$, the sections $\varepsilon_\infty,\varepsilon_0$, the component maps `comp`, the open `smoothLocus`, and the remaining fields of the structure. Let $O$ be a commutative ring with a ring homomorphism $\rho_O \colon R_q \to O$, let $\kappa$ be an algebraically closed field of characteristic $q$, and let $\mathrm{to}\kappa \colon O \to \kappa$ be a ring homomorphism. Writing $\mathrm{pr}_1$ for the first projection of the pullback of `DRLevel.toBase N₀ q` along $\operatorname{Spec}(\rho_O)$, the assertion is that both points $\mathfrak{X}.\xi_\infty(\rho_O,\mathrm{to}\kappa)$ and $\mathfrak{X}.\xi_0(\rho_O,\mathrm{to}\kappa)$ of that pullback lie in the open subset $\mathrm{pr}_1^{-1}(\mathfrak{X}.\mathrm{smoothLocus})$.
--
--   The two points $\xi_\infty$, $\xi_0$ are the generic points of the two components of the special fibre of the Deligne–Rapoport model of $X_0(N_0q)$ after base change to $O$ and reduction to $\kappa$; the statement is that they avoid the crossing (supersingular) points, so that the model is smooth there. It feeds the computation of the branch ideals at $\xi_\infty$ and $\xi_0$, the construction of a resolved model package with ramification data, and the integrality statement for germs at the generic points of the components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_xi_mem_preimage_smoothLocus.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.xi_mem_preimage_smoothLocus
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) :
    𝔛.ξinf ρO toκ ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) ⁻¹ᵁ 𝔛.smoothLocus) ∧
    𝔛.ξzero ρO toκ ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) ⁻¹ᵁ 𝔛.smoothLocus) := by sorry
