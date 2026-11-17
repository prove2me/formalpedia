-- Prove2me | Theorems.Thm_N25_qPlace_witnesses
-- name    : N25.qPlace_witnesses
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:03.461976+00:00
-- url     : https://prove2.me/theorems/80262b15-3a05-43b7-a149-7a9001aab533
-- title:
--   The rational and geometric $j$-series give simple-pole witnesses
-- statement:
--   Let $F_0=ℚ(X_H(25))$, let $F=ℚ̄(X_H(25))$, and let $jq$ be the formal $j$-Laurent series. There exist $j_0∈F_0$ and $j∈F$ whose Laurent expansions are respectively $jq$ over $ℚ$ and $ℚ̄$, with $j$ equal to the coefficient extension of $j_0$, and $$ord_q(j_0)=-1,\qquad ord_q(j)=-1.$$ This supplies compatible rational and geometric witnesses for the distinguished $q$-infinity place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open scoped MatrixGroups
open N25

theorem N25.qPlace_witnesses :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 H25
    let F := xHFunctionFieldBar 25 H25
    ∃ j₀ : F₀, ∃ j : F,
      (j₀ : LaurentSeries ℚ) = jqModC ℚ ∧
      (j : LaurentSeries K) = jqModC K ∧
      (j : LaurentSeries K) = coeffEmb K (j₀ : LaurentSeries ℚ) ∧
      (qSeriesBar ℚ F₀ j₀).order = -1 ∧
      (qSeriesBar K F j).order = -1 := by sorry
