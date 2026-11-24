-- Prove2me | Theorems.Thm_GlobalTheory_AwaySubalgebraEmbedding_exists_away_subalgebra_embedding
-- name    : GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:58:15.223846+00:00
-- url     : https://prove2.me/theorems/78defdf3-dfb2-4a7c-baf7-862959283053
-- title:
--   Away Subalgebra Embedding: exists away subalgebra embedding
-- statement:
--   The Away Subalgebra Embedding construction uses the exists away subalgebra embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsAwaySubalgebraEmbedding.lean#L5-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsAwaySubalgebraEmbedding.lean#L5-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAwaySubalgebraEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AwaySubalgebraEmbedding

theorem GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding (K : Type) [Field K] (S : Type) [CommRing S]
    [Algebra K S] (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ (κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x),
      (∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
        = algebraMap S (Localization.Away x) (s : S)) ∧
      Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ), ∀ s ∈ S₁,
        z * algebraMap S (Localization.Away x) x ^ m = algebraMap S (Localization.Away x) s →
          z ∈ AlgHom.range κ := by sorry
