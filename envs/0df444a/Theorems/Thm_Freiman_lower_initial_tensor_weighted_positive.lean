-- Prove2me | Theorems.Thm_Freiman_lower_initial_tensor_weighted_positive
-- name    : Freiman.lower_initial_tensor_weighted_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:31.930521+00:00
-- url     : https://prove2.me/theorems/09b2b5a2-2168-4bda-bf27-2c259a9cb030
-- title:
--   Freiman lower construction: initial tensor weighted positive
-- statement:
--   Strict positivity of a finite weighted sum; the source coefficients are positive and the nonnegative weights sum to one.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_tensor_weighted_positive (C : LowerInitialPoly) (x y z : ℝ)
    (hc : ∀ i j k : Fin 3, 0 < certFieldVal (C i j k))
    (hw : ∀ i j k : Fin 3, 0 ≤ lowerInitialWeight x y z i j k)
    (hs : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, lowerInitialWeight x y z i j k)=1) :
    0 < lowerInitialBernsteinEval C x y z := by
  sorry
