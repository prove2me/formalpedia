-- Prove2me | Theorems.Thm_GlobalTheory_MatchTerm_limit_class
-- name    : GlobalTheory.MatchTerm.limit_class
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:22:53.264988+00:00
-- url     : https://prove2.me/theorems/cac63eee-c937-4740-bf31-6e08ad4f1a63
-- title:
--   Match Term: limit class
-- statement:
--   The Match Term construction uses the limit class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L64-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']

theorem GlobalTheory.MatchTerm.limit_class {n : ℕ} (hn : 2 ≤ n) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (x : X) (α' : ℕ → X')
    (hα : ∀ j, ∃ μ, α' (j + 1) = α' j + n ^ j • μ)
    (hs : ∀ j, ∑' μ, σ' (α' j + n ^ j • μ) = c * ∑' μ, σ (x + n ^ j • μ)) :
    (∀ x', (∀ j, ∃ μ, x' = α' j + n ^ j • μ) → σ' x' = c * σ x) ∧
      (c * σ x ≠ 0 → ∃ x', ∀ j, ∃ μ, x' = α' j + n ^ j • μ) := by sorry
