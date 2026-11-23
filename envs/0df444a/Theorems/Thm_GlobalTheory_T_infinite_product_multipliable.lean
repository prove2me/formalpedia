-- Prove2me | Theorems.Thm_GlobalTheory_T_infinite_product_multipliable
-- name    : GlobalTheory.T.infinite_product_multipliable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:58.992579+00:00
-- url     : https://prove2.me/theorems/d63b46bf-7bff-495c-848c-84b91e0d15da
-- title:
--   T: infinite product multipliable
-- statement:
--   The T construction uses the infinite product multipliable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliableStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.infinite_product_multipliable : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by sorry
