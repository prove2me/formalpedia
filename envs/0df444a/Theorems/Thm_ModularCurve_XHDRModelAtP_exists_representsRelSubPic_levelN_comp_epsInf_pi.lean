-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_levelN_comp_epsInf_pi
-- name    : ModularCurve.XHDRModelAtP.exists_representsRelSubPic_levelN_comp_epsInf_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/9a0bb1e7-a789-5c6e-b0a0-063ee2660d72
-- title:
--   Representability of relative Pic⁰ for the level-M/p model
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and assume $p \mid M$ but $p^{2} \nmid M$; assume further that the $q$-expansion `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of the Laurent series field, and let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which bundles integral models of the modular curves of level $\Gamma_H(M)$ and of level `XHDRLevel.ΓN p M H hpM` over the base ring `XHDRLevel.R p` together with their properness, flatness, normality, smoothness and Galois-descent data. Write $c$ for the structure morphism `XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj` of the two-chart integral model attached to the function field `qExpFunctionFieldC ℚ (XHDRLevel.ΓN p M H hpM)` and the element `jAt`, over $\operatorname{Spec}$ of `XHDRLevel.R p`, and let $\varepsilon$ be the base-point of this model obtained from the fields of $\mathfrak{X}$ as $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$, a section of $c$ over the base. The assertion is that there is a designation $D$ consisting of a scheme $P$, a morphism $D.\mathrm{toBase} : P \to \operatorname{Spec}(\mathrm{XHDRLevel.R}\, p)$ and a section of it, such that: $D$ represents the sub-Picard condition `algEquivZeroCut`, i.e. there is a rigidified line bundle (Poincaré bundle) on $D.\mathrm{toBase}$ whose associated module is fibrewise algebraically equivalent to zero, such that for every scheme $T$ over the base and every rigidified line bundle on $T$ with that same fibrewise property there is a unique morphism $T \to P$ over the base pulling the Poincaré bundle back to a bundle isomorphic to the given one, the zero section pulling it back to the unit bundle; and moreover $D.\mathrm{toBase}$ is smooth, proper and geometrically connected.
--
--   This is the representability statement for the relative $\mathrm{Pic}^{0}$ of the smooth model of the modular curve of level $M/p$ (with the same $H$-structure) over the discrete valuation ring `XHDRLevel.R p`, rigidified along the cusp pushed forward by the degeneracy morphism; the resulting object plays the role of the Jacobian of that curve. It feeds the construction of the Néron-model data at $p$ for $J_H$, and is cited in the assembly of the level data and in the analysis of the fibres of multiplication by $N$ on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_levelN_comp_epsInf_pi.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open AlgebraicGeometry.SmoothProperCurve

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_representsRelSubPic_levelN_comp_epsInf_pi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃ D : RelativePic0Designation (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj),
      Nonempty (RepresentsRelSubPic (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry
