-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Counting_exists_ncard_entrywiseBox_le
-- name    : GlobalTheory.CompanionTheory.Counting.exists_ncard_entrywiseBox_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:33.044445+00:00
-- url     : https://prove2.me/theorems/9e2bbcc9-9d66-4e3c-9050-8f18f1c7211d
-- title:
--   Counting: exists ncard entrywise Box le
-- statement:
--   The Counting construction uses the exists ncard entrywise Box le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsNcardEntrywiseBoxLe.lean#L10-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsNcardEntrywiseBoxLe.lean#L10-L67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsNcardEntrywiseBoxLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Counting
open GroundTheory.Automorphic.CuspidalSpectrum

theorem GlobalTheory.CompanionTheory.Counting.exists_ncard_entrywiseBox_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ T i j) →
      (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)).Finite ∧
      ((Set.ncard (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)) : ℕ) : ℝ) ≤
        ∏ i, ∏ j, C * (1 + T i j) ^ Module.finrank ℚ K := by sorry
