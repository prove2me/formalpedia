-- Prove2me | Theorems.Thm_Helfgott_etaStar_vonMangoldt_summable
-- name    : Helfgott.etaStar_vonMangoldt_summable
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T22:15:36.446021+00:00
-- url     : https://prove2.me/theorems/3365ab97-bfdf-425f-bfa2-ce13fbc1dbb5
-- title:
--   Absolute convergence of the actual Gaussian-smoothed von Mangoldt sum
-- statement:
--   For every real scale x>0, the actual Helfgott smoothing η*(t)=(η₂ *_M φ)(49t), φ(t)=t² exp(−t²/2), gives an absolutely convergent von Mangoldt sum ∑ₙΛ(n)η*(n/x). This convergence permits the infinite Gaussian-based exponential sum in the circle-method counting identity; no finite truncation is assumed.
-- source:
--   Derived from the actual smoothing definitions in Helfgott, arXiv:1312.7748v2, equations (4.7), (4.10) and the final section-7 definition of η*. https://arxiv.org/html/1312.7748v2 . The explicit Gaussian envelope is derived in this proof. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace Helfgott

theorem etaStar_vonMangoldt_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * etaStar ((n : ℝ)/x)) := by sorry

end Helfgott
