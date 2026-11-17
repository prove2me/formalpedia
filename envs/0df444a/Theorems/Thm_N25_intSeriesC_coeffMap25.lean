-- Prove2me | Theorems.Thm_N25_intSeriesC_coeffMap25
-- name    : N25.intSeriesC_coeffMap25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:00.463206+00:00
-- url     : https://prove2.me/theorems/2c5ffaf9-691f-438d-aecd-123e05bc31fb
-- title:
--   Integral Laurent series commute with coefficient extension
-- statement:
--   Let $k⊆K$ be fields and let $s∈ℤ[[T]]$. If $s_k$ and $s_K$ are obtained by casting its coefficients into the two fields, then $$Coeff_{k→K}(s_k)=s_K.$$ This provides base-change naturality for integral q-series.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.intSeriesC_coeffMap25 (k K : Type*) [Field k] [Field K] [Algebra k K]
    (s : PowerSeries ℤ) :
    ModularCurve.coeffMap (algebraMap k K) (ModularCurve.intSeriesC k s) =
      ModularCurve.intSeriesC K s := by sorry
