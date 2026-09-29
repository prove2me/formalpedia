-- Prove2me | Theorems.Thm_Freiman_lowerJ_sign_binding
-- name    : Freiman.lowerJ_sign_binding
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:00:43.705363+00:00
-- url     : https://prove2.me/theorems/cbb0683a-39c2-4c08-9555-07778d282057
-- title:
--   Freiman repeated-three proof: sign binding
-- statement:
--   All28 printed expressions equal their exact four-coordinate source values.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_sign_binding : ∀ i : Fin 28, certFieldVal (lowerJSignFields i) = lowerJSigns i := by
  sorry
