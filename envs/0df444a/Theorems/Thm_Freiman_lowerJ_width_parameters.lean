-- Prove2me | Theorems.Thm_Freiman_lowerJ_width_parameters
-- name    : Freiman.lowerJ_width_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:00.622983+00:00
-- url     : https://prove2.me/theorems/d638e368-d6ae-457e-8c2c-141c022f14b4
-- title:
--   Freiman repeated-three proof: width parameters
-- statement:
--   The factor between (18/19)² and (19/18)² proves strict original-left normalization and the19/5 width criterion for every iterate.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_width_parameters (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (hn : lowerJSignFacts) (p : LowerPair) (k : ℕ) (hu : lowerJUpdated p k) (hr : (1/4:ℝ) ≤ lowerRatio ((lowerNormalize p).1++List.replicate k 3) ∧ lowerRatio ((lowerNormalize p).1++List.replicate k 3) ≤ (1/3:ℝ)) (hs : (1/4:ℝ) ≤ lowerRatio ((lowerNormalize p).2++List.replicate k 3) ∧ lowerRatio ((lowerNormalize p).2++List.replicate k 3) ≤ (1/3:ℝ)) (hq : (31/100:ℝ) < lowerScale ((lowerNormalize p).1++List.replicate k 3,(lowerNormalize p).2++List.replicate k 3) ∧ lowerScale ((lowerNormalize p).1++List.replicate k 3,(lowerNormalize p).2++List.replicate k 3) < (4/5:ℝ)) : lowerWidth ((lowerNormalize p).2++List.replicate k 3) ≤ lowerWidth ((lowerNormalize p).1++List.replicate k 3) ∧ lowerWidth ((lowerNormalize p).1++List.replicate k 3) < (19/5:ℝ)*lowerWidth ((lowerNormalize p).2++List.replicate k 3) := by
  sorry
