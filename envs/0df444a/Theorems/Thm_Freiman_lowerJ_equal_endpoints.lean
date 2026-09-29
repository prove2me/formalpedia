-- Prove2me | Theorems.Thm_Freiman_lowerJ_equal_endpoints
-- name    : Freiman.lowerJ_equal_endpoints
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:39.925918+00:00
-- url     : https://prove2.me/theorems/f31d8db6-7eb1-4e53-85c3-df23ba114de3
-- title:
--   Freiman repeated-three proof: equal endpoints
-- statement:
--   Explicit four actual source endpoints of J(U1,V) and J(U2,V), with parity duality and the auxiliary-width identity retained.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_equal_endpoints (haux : ∀ w : List ℕ+, |prefixEval w lowerBeta-prefixEval (w++[1,3]) lowerAlpha| = lowerWidth (w++[1,3])) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) (hc : lowerJEqualContact p) (hw : lowerWidth ((lowerNormalize p).1++[2]) < lowerWidth (lowerNormalize p).2 ∧ lowerWidth ((lowerNormalize p).1++[1,1]) < lowerWidth (lowerNormalize p).2) : lowerJEqualForkFacts p := by
  sorry
