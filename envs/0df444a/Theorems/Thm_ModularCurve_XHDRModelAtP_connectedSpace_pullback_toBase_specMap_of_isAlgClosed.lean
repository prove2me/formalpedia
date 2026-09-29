-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed
-- name    : ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/71b9f3d3-ac7f-541e-b842-ed5b10f8926a
-- title:
--   Geometric fibres of the Γ_H(M) model at p∣ M are connected
-- statement:
--   Fix a prime $p$ and a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a divisibility $p \mid M$. Assume $hj$: the Laurent series `jqModC` $\mathbb{Q}$, namely $q^{-1}$ times the integral power series `jNum` pushed into $\mathbb{Q}((q))$, lies in `qExpFunctionFieldC` $\mathbb{Q}$ $\top$, the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the ratios `intFormRatiosC` for the full group $\mathrm{SL}_2(\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, i.e. a bundle of data and properties for the two-chart integral model `X p (ΓM M H) hj` over $\operatorname{Spec}(\mathrm{R}\,p)$ and its structure morphism `toBase p (ΓM M H) hj`, which is the morphism out of the pushout of the two affine charts $\operatorname{Spec}$ of `chartAlgFin` and of `chartAlgInf` determined by their $\mathrm{R}\,p$-algebra structures; the components comprise properness, flatness, integrality, local finite presentation and normality on affine opens, properness and relative-dimension-one smoothness at the auxiliary level `ΓN p M H hpM`, an identification (`Meta`, `eeta`) of the base change to $\overline{\mathbb{Q}}$ with a curve model whose function field is `xHFunctionFieldBar M H`, Galois equivariance and a $q$-expansion normalisation on the finite chart, together with smoothness and geometric integrality of the generic fibre, all summarised here. Then for every algebraically closed field $L$ that is an algebra over `R p`, the underlying topological space of the fibre product of `toBase p (ΓM M H) hj` with $\operatorname{Spec}$ of the structure map $\mathrm{R}\,p \to L$ is connected (in particular nonempty).
--
--   This is the connectedness of all geometric fibres of the Deligne–Rapoport model of $X_H(M)$ over the local base at a prime $p$ dividing the level, the statement obtained classically from Zariski's connectedness theorem applied to the proper flat model together with the irreducibility of the generic fibre. It supplies the connectedness hypothesis used in the relative Picard package for this model: it is cited in the computation of global sections after base change ([`ModularCurve.XHDRModelAtP.bijective_algebraMap_sections_baseChange`](thm.html#ModularCurve.XHDRModelAtP.bijective_algebraMap_sections_baseChange)), in [`ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot`](thm.html#ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot), and in [`ModularCurve.XHDRModelAtP.not_smooth_pullback_snd_toBase_of_charP`](thm.html#ModularCurve.XHDRModelAtP.not_smooth_pullback_snd_toBase_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (L : Type) [Field L] [IsAlgClosed L] [Algebra (R p) L] :
    ConnectedSpace ↥(Limits.pullback (toBase p (ΓM M H) hj) (Scheme.TwoAffineOpenCover.specMap (R p) L)) := by sorry
