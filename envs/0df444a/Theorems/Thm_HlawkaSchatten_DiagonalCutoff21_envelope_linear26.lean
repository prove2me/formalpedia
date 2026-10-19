-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_envelope_linear26
-- name    : HlawkaSchatten.DiagonalCutoff21.envelope_linear26
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:12:39.148747+00:00
-- url     : https://prove2.me/theorems/2a7e995b-1cd2-4cec-82ed-fd666db9595a
-- title:
--   Envelope strictly below the linear threshold for all real p >= 26
-- statement:
--   For any real $p\ge26$, define
--
--   $$E_p(q)=\frac{1-q}{2(1-((1+q^p)/2)^{1/p})}.$$
--
--   At $q=197/500$ and $c=443/1000$ one has $E_p(q)<cp$. The assertion includes all real exponents above the endpoint, without an upper endpoint restriction. Together with the source paper's cyclic lower bound $cp<K_p$, it implies the required envelope comparison.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 2, equation (7), envelope comparison parameters in Table 1. This stronger linear comparison is proved by a rational endpoint certificate and Bernoulli scaling in formalization/Hlawka21/Envelope.lean.

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.envelope_linear26 {p : ℝ} (hp : 26 ≤ p) :
    scalarEnvelope p (197/500 : ℝ) < (443/1000 : ℝ)*p := by sorry
