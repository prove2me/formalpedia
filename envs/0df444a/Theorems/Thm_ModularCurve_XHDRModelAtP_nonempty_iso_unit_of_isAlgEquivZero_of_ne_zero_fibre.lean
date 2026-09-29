-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_fibre
-- name    : ModularCurve.XHDRModelAtP.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/efe911ac-0416-55c2-bae9-52d212b22ece
-- title:
--   Algebraically trivial invertible sheaves with a section on geometric fibres
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series $j$-expansion `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))`; let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, the bundle of data and properties for the integral model `toBase p (ΓM M H) hj` over `Spec (R p)` of the two-chart model of the level-$\Gamma_H(M)$ modular curve. The assertion is then: for every algebraically closed field $k$ and every morphism $x \colon \operatorname{Spec} k \to \operatorname{Spec}(R\,p)$, writing $X_x$ for the fibre product of `toBase p (ΓM M H) hj` and $x$ with structure morphism `pullback.snd`, and for every module $L$ on $X_x$ such that (i) $L$ is invertible, i.e. each point of $X_x$ has an open neighbourhood $U$ with the restriction of $L$ to $U$ isomorphic to the unit sheaf of $U$, and (ii) `IsAlgEquivZero` holds for `pullback.snd` and $L$: there are a scheme $T'$ with a morphism $h \colon T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, an invertible module $M'$ on $X_x \times_{\operatorname{Spec} k} T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M'$ along the base change of $t_0$ is isomorphic to the unit while its pullback along the base change of $t_1$ is isomorphic to the corresponding pullback of $L$; then every nonzero morphism $s$ from the monoidal unit of the category of modules on $X_x$ to $L$ forces $L$ to be isomorphic to that unit.
--
--   This is the statement that on each geometric fibre of the Deligne–Rapoport style integral model at level $\Gamma_H(M)$, an invertible sheaf that is algebraically equivalent to zero and carries a nonzero global section is trivial; for fibres of good reduction this is the usual fact for smooth proper geometrically integral curves, and for the fibre at $p$ it is obtained from the description of that fibre as two smooth curves glued along a reduced nonempty intersection. It serves as one of the hypotheses in the construction of the representing object for the relevant subfunctor of the relative Picard functor, and is used by [`ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le`](thm.html#ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_fibre.lean

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
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open AlgebraicGeometry.RelPicard

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_fibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p)))
      (L : (pullback (toBase p (ΓM M H) hj) x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd (toBase p (ΓM M H) hj) x) L →
      ∀ s : 𝟙_ (pullback (toBase p (ΓM M H) hj) x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback (toBase p (ΓM M H) hj) x).Modules) := by sorry
