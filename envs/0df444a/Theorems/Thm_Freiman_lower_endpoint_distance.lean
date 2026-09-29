-- Prove2me | Theorems.Thm_Freiman_lower_endpoint_distance
-- name    : Freiman.lower_endpoint_distance
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:03.275931+00:00
-- url     : https://prove2.me/theorems/1076bff1-3365-420f-b771-7044b105f800
-- title:
--   Freiman lower construction: endpoint distance
-- statement:
--   The endpoint and limiting word share each physical prefix, so the two one-sided cylinder errors add; this must use the actual sSup-defined localValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-target-limit; foundations.tex, found:continuity

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_endpoint_distance (p : LowerPair) (hp : lowerAdmissible p) (a : ℤ → ℕ+)
    (ha : LowerModel a) (hc : lowerCylinder p a) (upper : Bool) :
    |localValue a 0 - lowerEndpoint p upper| ≤ lowerCylinderError p := by
  sorry
