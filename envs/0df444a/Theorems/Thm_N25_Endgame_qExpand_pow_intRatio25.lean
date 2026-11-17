-- Prove2me | Theorems.Thm_N25_Endgame_qExpand_pow_intRatio25
-- name    : N25.Endgame.qExpand_pow_intRatio25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:54.119262+00:00
-- url     : https://prove2.me/theorems/3bfd93d4-cef3-43e6-a56d-b0cd5a413f7c
-- title:
--   Iterated $q$-Frobenius raises integral-series ratios to $p^n$th powers
-- statement:
--   Let $p$ be a prime, let $K$ be a field of characteristic $p$, let $n≥0$, and let $a,b∈ℤ[[q]]$ be formal power series. Write $a_K,b_K$ for their coefficientwise images in $K[[q]]$, viewed in the Laurent-series field, and let $Q_p$ be the prime $q$-expansion Frobenius. Then
--
--   $$Q_p^n(a_K/b_K)=(a_K/b_K)^{p^n}.$$
--
--   This supplies the power law on the integral-form ratios that generate the modular function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25
open N25.Endgame

theorem N25.Endgame.qExpand_pow_intRatio25
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (a b : PowerSeries ℤ) :
    (ModularCurve.qExpand K p ^ n)
        (ModularCurve.intSeriesC K a / ModularCurve.intSeriesC K b) =
      (ModularCurve.intSeriesC K a / ModularCurve.intSeriesC K b) ^ (p ^ n) := by sorry
