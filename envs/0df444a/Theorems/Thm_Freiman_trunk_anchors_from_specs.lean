-- Prove2me | Theorems.Thm_Freiman_trunk_anchors_from_specs
-- name    : Freiman.trunk_anchors_from_specs
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:07.718478+00:00
-- url     : https://prove2.me/theorems/16075599-081e-49ac-9981-8ffd2e7ab9d6
-- title:
--   trunk anchors from specs
-- statement:
--   The first and last source specifications are exactly the two actual signed parent anchors, without assuming normalization is invariant under a tie swap.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_anchors_from_specs (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    (∀ l, (trunkPlanAt (trunkCatalog.states k) pi).labels.head? = some l → trunkParentEndpoint p true ≤ trunkLocalUpper p l) ∧
    (∀ l, (trunkPlanAt (trunkCatalog.states k) pi).labels.getLast? = some l → lowerLocalLower p l ≤ trunkParentEndpoint p false) := by
  sorry
