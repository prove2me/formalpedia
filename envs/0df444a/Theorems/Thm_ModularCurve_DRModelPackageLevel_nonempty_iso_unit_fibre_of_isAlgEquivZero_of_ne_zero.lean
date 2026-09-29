-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero
-- name    : ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/5019c6b1-072a-55a6-894b-8e9bb8bf3dc0
-- title:
--   Algebraically trivial bundles with a section on geometric fibres
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime not dividing $N_0$, and let $\mathfrak P$ be a term of the structure `DRModelPackageLevel N₀ q hqN`, that is, the Deligne–Rapoport model data for the morphism `DRLevel.toBase N₀ q` from the Igusa-type scheme $X$ of level $N_0q$ to $\operatorname{Spec}(\mathrm{R}\,q)$: properness, flatness, integrality of the source and local finite presentation, integral closedness of the sections over each affine open, a curve model of the modular function field over $\overline{\mathbf Q}$ together with an isomorphism onto the $\overline{\mathbf Q}$-fibre compatible with the base and with the Galois action on places, a pinning of the Igusa chart by $q$-expansions, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbf Q$, the two sections $\varepsilon_\infty$, $\varepsilon_0$, and the remaining data of the package. The assertion is: for every algebraically closed field $k$, every morphism $x\colon\operatorname{Spec} k\to\operatorname{Spec}(\mathrm{R}\,q)$, writing $P$ for the fibre product of `DRLevel.toBase N₀ q` along $x$ and $p=$ `pullback.snd` $\colon P\to\operatorname{Spec} k$ for its second projection, and every module $L$ over $P$ such that (i) $L$ is invertible, in the sense that each point of $P$ has an open neighbourhood $U$ with the restriction of $L$ to $U$ isomorphic to the unit sheaf of $U$, and (ii) `IsAlgEquivZero p L` holds, that is, there are a scheme $T'$, a morphism $h\colon T'\to\operatorname{Spec} k$ that is locally of finite type and geometrically integral, an invertible module $M$ on the fibre product of $p$ with $h$, and two sections $t_0,t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M$ along the base change of $p$ by $t_0$ is isomorphic to the unit sheaf, while the pullback of $M$ along the base change by $t_1$ is isomorphic to the pullback of $L$; then every morphism $s$ from the monoidal unit of the category of modules on $P$ to $L$ with $s\neq 0$ forces $L$ to be isomorphic to that unit.
--
--   This is the rigidity statement for degree-zero line bundles on the geometric fibres of the Deligne–Rapoport model of $X_0(N_0q)$ over $\mathrm{R}\,q$: an invertible sheaf algebraically equivalent to zero and admitting a nonzero global section is trivial, both on the smooth fibres and on the special fibre made of two smooth curves meeting at the supersingular points. It supplies the fibrewise hypothesis in [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic), the representability of the rigidified relative $\mathrm{Pic}^0$-cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero.lean

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve
open AlgebraicGeometry.RelPicard

theorem ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q)))
      (L : (pullback (DRLevel.toBase N₀ q) x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd (DRLevel.toBase N₀ q) x) L →
      ∀ s : 𝟙_ (pullback (DRLevel.toBase N₀ q) x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback (DRLevel.toBase N₀ q) x).Modules) := by sorry
