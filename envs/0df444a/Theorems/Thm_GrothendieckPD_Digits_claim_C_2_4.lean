-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_claim_C_2_4
-- name    : GrothendieckPD.Digits.claim_C_2_4
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:18.520311+00:00
-- url     : https://prove2.me/theorems/1d2dd2ed-e3e7-4338-bd08-e405acc0cc0f
-- title:
--   Lemma C.2, Claim 4: the $H_{14}$ tail
-- statement:
--   For the bivariate threshold rounding function $F_*$ of §4.2, let $H_{14}$ be its kernel and write $[t^m]H_{14}$ for its degree-$m$ graded Hermite coefficient. Then the tail series is absolutely summable and satisfies
--
--   $$
--   \lambda_{14}\sum_{m>681}\bigl|[t^m]H_{14}(t)\bigr|
--    < 1.254728050780\cdot 10^{-6}.\qquad(C.31)
--   $$
--
--   This is Claim 4 in the proof of Lemma C.2. It isolates the Parseval estimate for $H_{14}$ from the arcsine estimates for the remaining graded linear thresholds.
--
--   **Formalization Note** The degrees $m>681$ are indexed by $m=k+682$ for $k\in\mathbb N$, and $[t^m]H_{14}$ is represented by `Hcoef 14 m`. Exact decimal notation denotes the corresponding rational real number.
-- source:
--   Heilman–Jones–Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820, Lemma C.2, Claim 4, Eq. (C.31), p. 34; proof via Eqs. (C.32)–(C.33), pp. 34–35. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

open GrothendieckPD.Digits

/-- Claim 4 in the proof of Lemma C.2, Eq. (C.31), p. 34: the weighted tail of the
bivariate-threshold kernel $H_{14}$ is below $1.254728050780\cdot 10^{-6}$ and is absolutely summable. -/
theorem GrothendieckPD.Digits.claim_C_2_4 :
    Summable (fun k => |Hcoef 14 (k + 682)|) ∧
      lam 14 * ∑' k, |Hcoef 14 (k + 682)| < (0.000001254728050780 : ℝ) := by sorry
