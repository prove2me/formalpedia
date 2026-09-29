-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
-- name    : ModularCurve.DRModelPackageLevel.eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/882d06d5-bcf1-51bf-b9c3-5c40a68b3c12
-- title:
--   Injectivity on closed points of πcirccomp₁ in characteristic p
-- statement:
--   Let $N_0\ge 1$ and let $p$ be a prime with $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`, that is, a bundle of data and properties attached to the Igusa scheme $X(N_0p)$ over $\mathrm{Spec}\,R_p$ (properness, flatness, integrality and local finite presentation of the structure map `toBase`, integral closedness on affine opens, an isomorphism `eeta` with a curve model `Meta` over $\overline{\mathbb Q}$ compatible with the Galois action and with the Igusa chart, smoothness and geometric integrality of the generic fibre, sections $\varepsilon_\infty,\varepsilon_0$ and further data, including a forgetful morphism $\pi$ over the base and the component morphisms `comp`). Let $\kappa$ be an algebraically closed field of characteristic $p$ and $\mathrm{to}\kappa \colon R_p \to \kappa$ a ring homomorphism. Write $\mathrm{fibre0}$ for the pullback of `toBase0` $=$ `igusaTo N₀ p` along $\mathrm{Spec}(\mathrm{to}\kappa)$, and $\mathrm{fibre}$ for the corresponding pullback of `toBase`; the morphism `fibreMap0 𝔓.π toκ` is the map $\mathrm{fibre} \to \mathrm{fibre0}$ induced on these pullbacks by the underlying morphism of $\mathfrak P.\pi$ (a morphism $X(N_0p)\to X_0(N_0)$ over $\mathrm{Spec}\,R_p$) together with the identity on the base. Let $x_1,x_2$ be points of the underlying space of $\mathrm{fibre0}$ whose singletons are closed, and suppose that the map on underlying topological spaces of the composite of `𝔓.comp κ toκ 1` (the component of the special fibre indexed by $1$, a morphism $\mathrm{fibre0} \to \mathrm{fibre}$) followed by `fibreMap0 𝔓.π toκ` sends $x_1$ and $x_2$ to the same point. Then $x_1 = x_2$.
--
--   Classically this is the statement that, on the special fibre in characteristic $p$, the forgetful map restricted to the second component is the Frobenius of $X_0(N_0)_\kappa$ (Deligne–Rapoport V.1.16), recorded here in the weaker points-level form that the resulting self-map of the fibre is injective on closed points. It is used in [`ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber`](thm.html#ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    (x₁ x₂ : ↥(fibre0 (N₀ := N₀) toκ)) (h₁ : IsClosed ({x₁} : Set ↥(fibre0 (N₀ := N₀) toκ)))
    (h₂ : IsClosed ({x₂} : Set ↥(fibre0 (N₀ := N₀) toκ)))
    (h : (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base x₁ = (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base x₂) :
    x₁ = x₂ := by sorry
