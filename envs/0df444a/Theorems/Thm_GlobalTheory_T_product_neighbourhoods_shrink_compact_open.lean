-- Prove2me | Theorems.Thm_GlobalTheory_T_product_neighbourhoods_shrink_compact_open
-- name    : GlobalTheory.T.product_neighbourhoods_shrink_compact_open
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:44.833606+00:00
-- url     : https://prove2.me/theorems/aa51d8dd-1082-4598-b7c9-bb06646ebab9
-- title:
--   T: product neighbourhoods shrink compact open
-- statement:
--   The T construction uses the product neighbourhoods shrink compact open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductNeighbourhoodsShrinkCompactOpenStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductNeighbourhoodsShrinkCompactOpenStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductNeighbourhoodsShrinkCompactOpen
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductNeighbourhoodsShrinkCompactOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.product_neighbourhoods_shrink_compact_open : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by sorry
