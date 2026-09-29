-- Prove2me | Theorems.Thm_Freiman_lowerJ_offered_domain
-- name    : Freiman.lowerJ_offered_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:14.728624+00:00
-- url     : https://prove2.me/theorems/a9dfb6a5-7cb2-4f79-8120-ff997e168a61
-- title:
--   Freiman repeated-three proof: offered domain
-- statement:
--   Translate exactly the offered H7 and strict N–N width conditions to the original normalized scalar parameter box.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_offered_domain (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerJDomain (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
  sorry
