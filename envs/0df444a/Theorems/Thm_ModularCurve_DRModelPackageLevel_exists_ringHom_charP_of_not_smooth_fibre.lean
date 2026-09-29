-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_ringHom_charP_of_not_smooth_fibre
-- name    : ModularCurve.DRModelPackageLevel.exists_ringHom_charP_of_not_smooth_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/7a2b00a7-5ed2-5c30-944b-128be1ff0121
-- title:
--   Non-smooth geometric fibres of the level model lie over q
-- statement:
--   Fix a natural number $N_0$ with $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a term of the structure `DRModelPackageLevel N₀ q hqN`, that is, a package of Deligne–Rapoport data for the morphism `DRLevel.toBase` $N_0\,q =$ `IgusaScheme.igusaTo` $(N_0q)\,q$ from the level-$N_0q$ modular scheme to $\operatorname{Spec}($ `DRLevel.R` $q)$: properness, flatness, integrality of the source and local finite presentation of this morphism, integral closedness of the sections over each affine open, a curve model over $\overline{\mathbf Q}$ with function field the base-changed modular function field of level $N_0q$ together with an isomorphism onto the corresponding geometric fibre, compatibility with the arithmetic Galois action and with the Igusa chart expansions, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbf Q$, and cusp sections, among further fields. Let $k$ be an algebraically closed field and let $s \colon \operatorname{Spec}(k) \to \operatorname{Spec}($ `DRLevel.R` $q)$ be a morphism of schemes such that the second projection of the pullback of `DRLevel.toBase` $N_0\,q$ along $s$ — the fibre of the model at the geometric point $s$ — is not smooth. Then there exist a ring homomorphism $\tau \colon$ `DRLevel.R` $q \to k$ and a proof that $k$ has characteristic $q$ such that $s = \operatorname{Spec}(\tau)$. Of the package, only the smoothness of the fibre over $\mathbf Q$ enters the proof.
--
--   This is the statement that the Deligne–Rapoport model of level $N_0q$ over the base `DRLevel.R` $q$ has smooth geometric fibres away from $q$, so that any geometric point with non-smooth fibre is a point of the closed fibre, in characteristic $q$. It is used in the analysis of the fibre at $q$ of this model, in particular by [`ModularCurve.DRModelPackageLevel.fibre_wL_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange`](thm.html#ModularCurve.DRModelPackageLevel.fibre_wL_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange) and [`ModularCurve.DRModelPackageLevel.twoGluedSmoothCurveDegenerations`](thm.html#ModularCurve.DRModelPackageLevel.twoGluedSmoothCurveDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_ringHom_charP_of_not_smooth_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.DRModelPackageLevel.exists_ringHom_charP_of_not_smooth_fibre
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    {k : Type} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q)))
    (hns : ¬ Smooth (pullback.snd (DRLevel.toBase N₀ q) s)) :
    ∃ (toκ : DRLevel.R q →+* k) (_ : CharP k q), s = Spec.map (CommRingCat.ofHom toκ) := by sorry
