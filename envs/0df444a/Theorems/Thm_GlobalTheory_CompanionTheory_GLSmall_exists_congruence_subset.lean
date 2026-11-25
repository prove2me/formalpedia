-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLSmall_exists_congruence_subset
-- name    : GlobalTheory.CompanionTheory.GLSmall.exists_congruence_subset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:57.165468+00:00
-- url     : https://prove2.me/theorems/345f8723-27dd-5a8f-81e4-660079bc16fa
-- title:
--   GLSmall: exists congruence subset
-- statement:
--   The GLSmall construction uses the exists congruence subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean#L40-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean#L40-L68

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.GLSmall.exists_congruence_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), IsOpen U →
    (1 : GL (Fin n) k) ∈ U → ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ g : GL (Fin n) k,
    (∀ i j, ∃ μ ∈ 𝒪[k], (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j = ϖ ^ l * μ) →
    (∀ i j, ∃ μ ∈ 𝒪[k], ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j = ϖ ^ l * μ) →
    g ∈ U := by sorry
