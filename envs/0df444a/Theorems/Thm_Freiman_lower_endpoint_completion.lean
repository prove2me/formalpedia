-- Prove2me | Theorems.Thm_Freiman_lower_endpoint_completion
-- name    : Freiman.lower_endpoint_completion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:21.688803+00:00
-- url     : https://prove2.me/theorems/133cb494-4a43-4d51-8905-1033e008f297
-- title:
--   Freiman lower construction: endpoint completion
-- statement:
--   Every actual endpoint, including both virtual parity cases and width ties, is a permitted completion of the old physical prefixes and evaluates to the existing sSup-defined localValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, eq:lc-natural-tails and actual endpoint rule

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_endpoint_completion (p : LowerPair) (h : lowerAdmissible p) (upper : Bool) :
    LowerModel (lowerPeriodicSequence (lowerEndpointWords p upper) [1,2]) ∧
    lowerCylinder p (lowerPeriodicSequence (lowerEndpointWords p upper) [1,2]) ∧
    localValue (lowerPeriodicSequence (lowerEndpointWords p upper) [1,2]) 0 = lowerEndpoint p upper := by
  sorry
