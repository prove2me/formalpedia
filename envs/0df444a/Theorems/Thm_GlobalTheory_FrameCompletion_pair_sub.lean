-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_pair_sub
-- name    : GlobalTheory.FrameCompletion.pair_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:11.144882+00:00
-- url     : https://prove2.me/theorems/7b2695ad-e6e8-40c0-93ad-3941f0f7bce9
-- title:
--   Frame Completion: pair sub
-- statement:
--   The Frame Completion construction uses the pair sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L77-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}

theorem GlobalTheory.FrameCompletion.pair_sub {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (M : Matrix κ κ L)
    (c : L) : cT σ (X - c • (W * M)) * Q * (X - c • (W * M)) =
      cT σ X * Q * X - c • (cT σ X * Q * W * M) - σ c • (cT σ M * (cT σ W * Q * X)) +
        (σ c * c) • (cT σ M * (cT σ W * Q * W) * M) := by sorry
