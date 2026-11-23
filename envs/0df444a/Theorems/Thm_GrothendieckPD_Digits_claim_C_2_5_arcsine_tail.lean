-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5_arcsine_tail
-- name    : GrothendieckPD.Digits.claim_C_2_5_arcsine_tail
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:55.546591+00:00
-- url     : https://prove2.me/theorems/3c8924e7-a3bf-4d55-9c0f-8d7b30933c85
-- title:
--   Claim 5 of Lemma C.2: arcsine head–tail bounds for $H_{19},\ldots,H_{31}$
-- statement:
--   For every $19\le i\le31$, let $P_{i,+}$ be the correlation polynomial from Table 1 with all coefficients replaced by their absolute values, and put
--   $$A_i=\sum_{m=1}^{681}[t^m]\left(\frac{2}{\pi}\arcsin P_{i,+}(t)\right).$$
--   Then the tail of the graded linear-threshold kernel $H_i$ converges absolutely and satisfies
--   $$\sum_{m>681}\bigl|[t^m]H_i(t)\bigr|\le 1-A_i.$$
--
--   This is the arcsine majorant estimate in Eqs. (C.35)–(C.36). It uses the kernel identity $H_i=(2/\pi)\arcsin P_i$ from (C.4), the coefficient comparison from (C.8), nonnegativity of the arcsine coefficients, and the total majorant mass $(2/\pi)\arcsin P_{i,+}(1)\le1$. The statement deliberately asserts an inequality for `Hcoef`, rather than identifying the Hermite coefficient function with a polynomial arcsine coefficient without proof.
--
--   **Formalization Note** The integer $m>681$ is indexed as $m=k+682$, and $A_i$ is `arcsinHead i` in the published arcsine-tail definition module.
-- source:
--   Heilman–Jones–Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820, proof of Lemma C.2, Claim 5, Eqs. (C.35)–(C.36), p. 35, using Eq. (C.4) and Eq. (C.8), p. 24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_ArcsineTail

open GrothendieckPD.Digits

/-- Eqs. (C.4), (C.8), and (C.35)--(C.36), pp. 24 and 35: the arcsine majorant
bounds every graded linear-threshold tail for `i = 19, ..., 31` by one minus its
finite nonnegative head, and the tail converges absolutely. -/
theorem GrothendieckPD.Digits.claim_C_2_5_arcsine_tail :
    ∀ i ∈ Finset.Icc 19 31,
      (Summable fun k => |Hcoef i (k + 682)|) ∧
        (∑' k, |Hcoef i (k + 682)|) ≤ 1 - arcsinHead i := by sorry
