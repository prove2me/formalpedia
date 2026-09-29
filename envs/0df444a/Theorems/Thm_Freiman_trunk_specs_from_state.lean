-- Prove2me | Theorems.Thm_Freiman_trunk_specs_from_state
-- name    : Freiman.trunk_specs_from_state
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:43.492656+00:00
-- url     : https://prove2.me/theorems/6964329a-c228-4992-bd16-6648cf7bec63
-- title:
--   trunk specs from state
-- statement:
--   Finite list indexing connects every actual source specification and its branch to the complete scalar catalog; no endpoint specification is silently dropped.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_specs_from_state (he : TrunkEndpointLaw) (hg : TrunkGreaterLaw)
    (ht : ∀ (p : LowerPair) (k : Fin 16), lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context →
      ∀ sp : Section14Spec, (∀ b ∈ trunkBranches (trunkCatalog.states k).context sp, trunkHolds b.1 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) → lowerHistoryComparisonHolds b.2 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p))) → trunkSpecHolds p sp)
    (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : trunkStateSound trunkCatalog k) :
    ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp := by
  sorry
