-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5
-- name    : GrothendieckPD.Digits.claim_C_2_5
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:30.906465+00:00
-- url     : https://prove2.me/theorems/c81af3bf-2d3b-44ba-97e6-be8b2c89a9bc
-- title:
--   Lemma C.2, Claim 5: tails of $H_{17},\ldots,H_{31}$
-- statement:
--   For the graded linear-threshold pairs $(f_i,g_i)$, $17\le i\le31$, from §4.2, all absolute tail series of their kernels $H_i$ converge, and
--
--   $$
--   \sum_{i=17}^{31}\lambda_i\sum_{m>681}\bigl|[t^m]H_i(t)\bigr|
--    < 2.623422117515\cdot 10^{-6}.\qquad(C.34)
--   $$
--
--   This is Claim 5 in the proof of Lemma C.2. The source derives it using the arcsine expansion, the finite-head bound (C.36) for $19\le i\le31$, and the Cauchy estimates (C.37) for $i=17,18$.
--
--   **Formalization Note** The degrees $m>681$ are indexed by $m=k+682$ for $k\in\mathbb N$, and $[t^m]H_i$ is represented by `Hcoef i m`. Exact decimal notation denotes the corresponding rational real number.
-- source:
--   Heilman–Jones–Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820, Lemma C.2, Claim 5, Eq. (C.34), p. 35; proof via Eqs. (C.35)–(C.37), pp. 35–36. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

open GrothendieckPD.Digits

/-- Claim 5 in the proof of Lemma C.2, Eq. (C.34), p. 35: the combined weighted tails of
the graded linear-threshold kernels $H_{17},\ldots,H_{31}$ are absolutely summable and bounded. -/
theorem GrothendieckPD.Digits.claim_C_2_5 :
    (∀ i ∈ Finset.Icc 17 31, Summable fun k => |Hcoef i (k + 682)|) ∧
      ∑ i ∈ Finset.Icc 17 31, lam i * ∑' k, |Hcoef i (k + 682)| <
        (0.000002623422117515 : ℝ) := by sorry
