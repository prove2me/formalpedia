-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BigCell_preimage_box_shrinking
-- name    : GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:21:03.097822+00:00
-- url     : https://prove2.me/theorems/5c9be773-8ee5-4617-a20b-009c547ae110
-- title:
--   Big Cell: preimage box shrinking
-- statement:
--   The Big Cell construction uses the preimage box shrinking property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductNeighbourhoodsShrinkCompactOpen.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductNeighbourhoodsShrinkCompactOpen.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductNeighbourhoodsShrinkCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BigCell

theorem GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by sorry
