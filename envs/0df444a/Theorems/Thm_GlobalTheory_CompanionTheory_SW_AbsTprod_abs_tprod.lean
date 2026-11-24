-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_abs_tprod
-- name    : GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:59.024899+00:00
-- url     : https://prove2.me/theorems/93e9c406-bde7-426f-a203-b8827e84988a
-- title:
--   Abs Tprod: abs tprod
-- statement:
--   The Abs Tprod construction uses the abs tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L39-L45

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsTprod

theorem GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by sorry
