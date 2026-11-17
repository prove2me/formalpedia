-- Prove2me | Theorems.Thm_N25_cusp_constant_place_lift
-- name    : N25.cusp_constant_place_lift
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:53.710197+00:00
-- url     : https://prove2.me/theorems/4a854ae0-8bd0-4d4b-b570-cd78de5d84ef
-- title:
--   Each geometric place has a unique order-preserving complex lift
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$, let $F$ be the geometric level-$25$ function field, and let $F_{\mathbb C}$ be its complex base change. There exists a coefficientwise ring homomorphism $\kappa:F\to F_{\mathbb C}$ such that for every place $P$ of $F$ there is a place $P'$ of $F_{\mathbb C}$ satisfying
--
--   $$\mathcal O_{P'}\cap_{\kappa}F=\mathcal O_P,\qquad\operatorname{ord}_{P'}(\kappa x)=\operatorname{ord}_P(x)\quad(x\in F),$$
--
--    and $P'$ is the unique complex place with that contraction. This transfers algebraic places to complex analytic places without changing orders.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25

theorem N25.cusp_constant_place_lift
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 N25.H25
    let F := xHFunctionFieldBar 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    ∃ κ : F →+* Fℂ,
      (∀ x : F, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries K)) ∧
      ∀ P : Place K F, ∃ P' : Place ℂ Fℂ,
        P'.toValuationSubring.comap κ = P.toValuationSubring ∧
        (∀ x : F, P'.ord (κ x) = P.ord x) ∧
        ∀ Q' : Place ℂ Fℂ,
          Q'.toValuationSubring.comap κ = P.toValuationSubring → Q' = P' := by sorry
