-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_pair_comb
-- name    : GlobalTheory.FrameCompletion.pair_comb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:38.427848+00:00
-- url     : https://prove2.me/theorems/a9d25dfd-8405-4882-8a48-db5f7ee45849
-- title:
--   Frame Completion: pair comb
-- statement:
--   The Frame Completion construction uses the pair comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L69-L75

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

theorem GlobalTheory.FrameCompletion.pair_comb {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (s t s' t' : L) :
    cT σ (s • X + t • W) * Q * (s' • X + t' • W) =
      (σ s * s') • (cT σ X * Q * X) + (σ s * t') • (cT σ X * Q * W) + (σ t * s') • (cT σ W * Q * X) +
        (σ t * t') • (cT σ W * Q * W) := by sorry
