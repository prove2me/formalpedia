-- Prove2me | Theorems.Thm_GlobalTheory_PadicEmb_exists_embedding
-- name    : GlobalTheory.PadicEmb.exists_embedding
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:39.93682+00:00
-- url     : https://prove2.me/theorems/444ba104-9f2a-4a75-92c9-4728018bcda8
-- title:
--   Padic Emb: exists embedding
-- statement:
--   The Padic Emb construction uses the exists embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOneOfFinitePadicIntDomain.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOneOfFinitePadicIntDomain.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicEmb

theorem GlobalTheory.PadicEmb.exists_embedding : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D]
    [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 →
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by sorry
