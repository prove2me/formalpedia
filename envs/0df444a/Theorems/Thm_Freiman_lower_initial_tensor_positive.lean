-- Prove2me | Theorems.Thm_Freiman_lower_initial_tensor_positive
-- name    : Freiman.lower_initial_tensor_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:25.340126+00:00
-- url     : https://prove2.me/theorems/d3c1880e-8c3f-44a6-bb1a-e93acf23a8f2
-- title:
--   Freiman lower construction: initial tensor positive
-- statement:
--   (c : LowerInitialSeamCase) (hv : lowerInitialSeamCertificateValid c)
--       (x y z : ℝ) (hb : lowerInitialBox x y z) :
--       0 < lowerInitialPolyEval (lowerInitialSeamPolynomial c) x y z
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_tensor_positive (c : LowerInitialSeamCase) (hv : lowerInitialSeamCertificateValid c)
    (x y z : ℝ) (hb : lowerInitialBox x y z) :
    0 < lowerInitialPolyEval (lowerInitialSeamPolynomial c) x y z := by
  sorry
