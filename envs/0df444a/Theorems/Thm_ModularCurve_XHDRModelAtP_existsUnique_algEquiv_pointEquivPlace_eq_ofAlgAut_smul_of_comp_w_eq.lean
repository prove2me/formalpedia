-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_existsUnique_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
-- name    : ModularCurve.XHDRModelAtP.existsUnique_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/97d46cdd-9bca-553b-8a11-e44558fd0f6e
-- title:
--   Function-field automorphism attached to X.w: existence, uniqueness
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis `hj` that the $q$-expansion $j(q)$ over $\mathbb{Q}$ lies in the subfield $\mathbb{Q}$-generated inside $\mathbb{Q}((q))$ by the integral weight-ratio functions for the full group $\mathrm{SL}(2,\mathbb{Z})$; let $\mathfrak{X}$ be an inhabitant of the structure `XHDRModelAtP p M H hpM hj`, which bundles a proper flat integral two-chart model of $X_{\Gamma_H(M)}$ over $R_p$, a curve model `𝔛.Meta` of the field $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ (the base change `xHFunctionFieldBar M H` of the function field to $\overline{\mathbb{Q}}$ inside Laurent series) together with an isomorphism `𝔛.eeta` of its underlying scheme with the geometric generic fibre, a Galois-equivariance condition, a normalisation of the chart functions, and a distinguished automorphism `𝔛.w` of the model, all summarised by the structure. The assertion is that there is exactly one $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H` with the following property: for all sections $y,y'$ of `𝔛.Meta.toBase` over $\mathrm{Spec}\,\overline{\mathbb{Q}}$, if transporting $y'$ through `𝔛.eeta` and the projection to the integral model and then applying `𝔛.w.hom` gives the same $\overline{\mathbb{Q}}$-point of the integral model as transporting $y$, then the place of `xHFunctionFieldBar M H` corresponding to $y'$ under the bijection `𝔛.Meta.pointEquivPlace` is the image of the place corresponding to $y$ under the action of the semilinear automorphism $(\theta,\mathrm{id})$, i.e. the valuation subring of the place of $y$ is carried over by $\theta$.
--
--   This packages the distinguished automorphism of a Deligne–Rapoport-style model at a prime $p$ exactly dividing the level as a single automorphism of the geometric function field, characterised by its effect on places (local rings at closed points), with no modular description of that automorphism asserted. It is used in the study of the Néron model of the Jacobian $J_H$ at $p$, for instance in the computations of toric and corner subgroups attached to an Abel–Jacobi normalisation and a choice of such $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_existsUnique_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.existsUnique_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃! θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H),
      ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y := by sorry
