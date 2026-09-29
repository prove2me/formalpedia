-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_smoothOfRelativeDimension_one_smoothLocus_and_maximal
-- name    : ModularCurve.XHDRModelAtP.smoothOfRelativeDimension_one_smoothLocus_and_maximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f7d321ad-2a2d-5736-af0b-c29449a3223d
-- title:
--   Smooth locus of the Γ_H(M) model: smooth and maximal
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, together with divisibility hypotheses $p \mid M$ and $p^2 \nmid M$, and assume $hj$: the Laurent series `jqModC` $\mathbb{Q}$ — namely $q^{-1}$ times the power series with the integral $j$-coefficients — lies in the subfield `qExpFunctionFieldC` $\mathbb{Q}$ of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the full-level form ratios `intFormRatiosC`. Let $\mathfrak{X}$ be a term of the bundle `XHDRModelAtP p M H hpM hj`, i.e. the package of data and axioms (properness, flatness, integrality, local finite presentation over the base, normality of affine sections, a smooth model at the auxiliary level `ΓN`, an identification of the geometric fibre over $\overline{\mathbb{Q}}$ with a curve model whose function field is `xHFunctionFieldBar M H`, with Galois equivariance and $q$-expansion pinning, generic smoothness and geometric integrality, and further fields, summarised here) for the scheme `X p (ΓM M H) hj` — the two-chart integral model obtained by glueing $\mathrm{Spec}$ of the two chart algebras in `qExpFunctionFieldC` $\mathbb{Q}$ `(ΓM M H)` — with its structure morphism `toBase p (ΓM M H) hj` to $\mathrm{Spec}$ of `R p`. The conclusion is twofold: first, the open immersion of $\mathfrak{X}$`.smoothLocus` followed by `toBase p (ΓM M H) hj` is smooth of relative dimension $1$; second, every open subscheme $W$ of `X p (ΓM M H) hj` whose immersion followed by `toBase` is smooth of relative dimension $1$ satisfies $W \le \mathfrak{X}$`.smoothLocus`.
--
--   This records that the distinguished open `smoothLocus` of the Deligne–Rapoport-type model at $p$ of the modular curve of level $\Gamma_H(M)$ is indeed the largest open on which the structure morphism to the base is smooth of relative dimension one. It is the instance of the smooth-locus hypothesis required by the representability statement for the relative Picard functor of this model, [`ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le`](thm.html#ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_smoothOfRelativeDimension_one_smoothLocus_and_maximal.lean

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

theorem ModularCurve.XHDRModelAtP.smoothOfRelativeDimension_one_smoothLocus_and_maximal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    SmoothOfRelativeDimension 1 (𝔛.smoothLocus.ι ≫ (toBase p (ΓM M H) hj)) ∧
    (∀ W : (X p (ΓM M H) hj).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (toBase p (ΓM M H) hj)) → W ≤ 𝔛.smoothLocus) := by sorry
