-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5_cauchy_tail
-- name    : GrothendieckPD.Digits.claim_C_2_5_cauchy_tail
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:22.79353+00:00
-- url     : https://prove2.me/theorems/8219bea2-68d4-4e21-a585-f90ef781d2df
-- title:
--   Claim 5 of Lemma C.2: exceptional Cauchy tails for $H_{17}$ and $H_{18}$
-- statement:
--   The exceptional tails in Claim 5 of Lemma C.2 converge absolutely and obey
--   $$\sum_{m>681}\bigl|[t^m]H_{17}(t)\bigr|<6.982\cdot10^{-54},
--   \qquad
--   \sum_{m>681}\bigl|[t^m]H_{18}(t)\bigr|<1.223\cdot10^{-13}.$$
--
--   These are the two bounds in Eq. (C.37). In the source they follow from Cauchy's estimate on the circles $R=6/5$ and $R=21/20$, respectively, the bounds on $|\Re P_i(z)|$ by $\eta=19/20$ and $\eta=49/50$, the resulting arcsine estimate, and oddness of $H_i$.
--
--   **Formalization Note** Degrees $m>681$ are indexed by $m=k+682$. Scientific-decimal literals denote the corresponding exact rational real numbers.
-- source:
--   Heilman–Jones–Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820, proof of Lemma C.2, Claim 5, Eq. (C.37), p. 36 (parameters and arcsine estimate on p. 35). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

open GrothendieckPD.Digits

/-- Eq. (C.37), p. 36: the exceptional tails for `i = 17, 18`, obtained by
Cauchy's estimate, converge absolutely and satisfy the stated strict bounds. -/
theorem GrothendieckPD.Digits.claim_C_2_5_cauchy_tail :
    ((Summable fun k => |Hcoef 17 (k + 682)|) ∧
        (∑' k, |Hcoef 17 (k + 682)|) < (6.982e-54 : ℝ)) ∧
      ((Summable fun k => |Hcoef 18 (k + 682)|) ∧
        (∑' k, |Hcoef 18 (k + 682)|) < (1.223e-13 : ℝ)) := by sorry
