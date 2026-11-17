-- Prove2me | Theorems.Thm_N25_cusp_complex_endpoints
-- name    : N25.cusp_complex_endpoints
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:13.544102+00:00
-- url     : https://prove2.me/theorems/646e04e6-e094-4de7-831c-e92cba2ebbb8
-- title:
--   Integral cusp matrices give normalized complex endpoints
-- statement:
--   Let $\Gamma=\Gamma_H(25)$ and let $F_{\mathbb C}$ be the complex level-$25$ function field. For $B=(b_{ij})\in\mathrm{SL}_2(\mathbb Z)$ define $w(B)=1$ if $b_{21}\equiv0\pmod{25}$, $w(B)=5$ if $5\mid b_{21}$ but $25\nmid b_{21}$, and $w(B)=25$ otherwise. There exist an element $j_{\mathbb C}\in F_{\mathbb C}$ with the standard $j$-series and places $P_B$ such that
--
--   $$\operatorname{ord}_{P_B}(j_{\mathbb C})=-w(B),$$
--
--    $x\in\mathcal O_{P_B}$ exactly when the realization $x(B\tau)$ has a finite limit at infinity, and for every nonzero $x$ there is $L\ne0$ with $x(B\tau)\exp(-2\pi i\operatorname{ord}_{P_B}(x)\tau/w(B))\to L$. This is the normalized analytic cusp dictionary used in the cusp census.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index

set_option autoImplicit false
open ModularCurve AlgebraicCurve CongruenceSubgroup
open scoped MatrixGroups Topology
open N25

theorem N25.cusp_complex_endpoints :
    let Γ := CohCarrier.GammaH 25 N25.H25
    let F₀ := xHFunctionField 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    let width : SL(2, ℤ) → ℕ := fun B =>
      let c := (B 1 0 : ZMod 25).val
      if c = 0 then 1 else if c % 5 = 0 then 5 else 25
    ∃ jℂ : Fℂ, ∃ endpoint : SL(2, ℤ) → Place ℂ Fℂ,
      (jℂ : LaurentSeries ℂ) = jqModC ℂ ∧
      (∀ B : SL(2, ℤ), (endpoint B).ord jℂ = -(width B : ℤ)) ∧
      (∀ B : SL(2, ℤ), ∀ x : Fℂ,
        x ∈ (endpoint B).toValuationSubring ↔
          ∃ L : ℂ, Filter.Tendsto
            (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (B • τ))
            UpperHalfPlane.atImInfty (𝓝 L)) ∧
      (∀ B : SL(2, ℤ), ∀ x : Fℂ, x ≠ 0 →
        ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto
          (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (B • τ) *
            Complex.exp (-(2 * Real.pi * Complex.I *
              ((endpoint B).ord x : ℂ) * (τ : ℂ) / (width B : ℂ))))
          UpperHalfPlane.atImInfty (𝓝 L)) := by sorry
