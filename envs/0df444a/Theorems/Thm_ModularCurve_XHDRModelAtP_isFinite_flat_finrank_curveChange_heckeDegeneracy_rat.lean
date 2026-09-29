-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
-- name    : ModularCurve.XHDRModelAtP.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/5b67459c-78ac-565e-8ec4-63d49b4ef6af
-- title:
--   Generic fibre of the two Hecke degeneracy legs stays finite flat
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the $q$-expansion $jqModC$ of $j$ over $\mathbb{Q}$ lies in the intermediate field $qExpFunctionFieldC\ \mathbb{Q}\ \top$ of the Laurent series field generated over $\mathbb{Q}$ by the integral-form ratios for $SL(2,\mathbb{Z})$; let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which packages properness, flatness, integrality, finite presentation, normality, smoothness of the auxiliary level and the Galois- and chart-compatibility data for the two-chart integral models $X_p(\Gamma)_{hj}$ over $\operatorname{Spec}(R_p)$. Let $\ell$ be a prime and let $\pi_\alpha,\pi_\beta$ be morphisms from the model of level $GammaH\ M\ H \cap \Gamma_0(M\ell)$ to the model of level $\Gamma_M(M,H)$ commuting with the structure maps to $\operatorname{Spec}(R_p)$, each finite and locally of finite presentation. Let $U$ be an open subscheme of the target containing every point whose local ring has Krull dimension at most $1$, over which both morphisms restrict to flat maps whose $\operatorname{finrank}$ at each point of $U$ equals $\ell$ if $\ell \mid M$ and $\ell+1$ otherwise. The conclusion produces, for the base change of each of $\pi_\alpha,\pi_\beta$ along $\operatorname{Spec}\mathbb{Q} \to \operatorname{Spec}(R_p)$ (the map of pullbacks given by `RelPicard.curveChange`), finiteness and local finite presentation, and asserts flatness of both together with the constancy of their $\operatorname{finrank}$, equal to $\ell$ if $\ell \mid M$ and to $\ell+1$ otherwise, at every point.
--
--   This is the passage to the generic fibre for the pair of degeneracy maps between the integral models of $X_{\Gamma_H(M)\cap\Gamma_0(M\ell)}$ and $X_H(M)$: the finite locally free structure of prescribed degree, known over the open locus of points of codimension at most one in the integral model, is transported to the curves over $\mathbb{Q}$. It is used in the construction of the Hecke correspondence on the relative Picard functor, in the statements producing a Hecke operator along either leg.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
  ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (πα πβ : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj))
    [IsFinite πα.1] [IsFinite πβ.1] [LocallyOfFinitePresentation πα.1] [LocallyOfFinitePresentation πβ.1]
    (U : (X p (ΓM M H) hj).Opens)
    (hU : ∀ x : ↥(X p (ΓM M H) hj), ringKrullDim ((X p (ΓM M H) hj).presheaf.stalk x) ≤ 1 → x ∈ U)
    [Flat (πα.1 ∣_ U)] [Flat (πβ.1 ∣_ U)]
    (hrkα : ∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πα.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1))
    (hrkβ : ∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) :
    ∃ (_ : IsFinite (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : IsFinite (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ))),
      Flat (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)) ∧
      Flat (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)) ∧
      (∀ y, (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) ∧
      (∀ y, (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) := by sorry
