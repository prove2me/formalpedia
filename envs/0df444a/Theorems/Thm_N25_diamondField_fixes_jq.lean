-- Prove2me | Theorems.Thm_N25_diamondField_fixes_jq
-- name    : N25.diamondField_fixes_jq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:10.132231+00:00
-- url     : https://prove2.me/theorems/3ae9cab6-be92-4709-84ec-7c7505e67a41
-- title:
--   Every diamond automorphism fixes the geometric $j$-function
-- statement:
--   Let $d\in(\mathbb Z/25\mathbb Z)^\times$, let $j_0$ be an element of the rational level-$25$ function field whose Laurent series is the standard $j$-series, and let $j$ be its coefficient extension to $\overline{\mathbb Q}$. Then the diamond automorphism $\delta_d$ fixes $j$:
--
--   $$\delta_d(j)=j.$$
--
--   This confirms that the modular $j$-map descends through the diamond quotient.
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

theorem N25.diamondField_fixes_jq
    (d : (ZMod 25)ˣ) (j₀ : xHFunctionField 25 H25)
    (hj₀ : (j₀ : LaurentSeries ℚ) = jqModC ℚ) :
    let j : xHFunctionFieldBar 25 H25 :=
      ⟨coeffEmb (AlgebraicClosure ℚ) (j₀ : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j₀.2⟩
    diamondAutHBar 25 H25 d j = j := by sorry
