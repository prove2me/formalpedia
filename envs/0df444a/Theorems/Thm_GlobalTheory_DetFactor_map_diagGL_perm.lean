-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_map_diagGL_perm
-- name    : GlobalTheory.DetFactor.map_diagGL_perm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:13.665056+00:00
-- url     : https://prove2.me/theorems/3c2865e3-abf3-4c1c-be6e-097649c1fc3d
-- title:
--   Det Factor: map diag GL perm
-- statement:
--   The Det Factor construction uses the map diag GL perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L62-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}

theorem GlobalTheory.DetFactor.map_diagGL_perm {n : ℕ} (c : GL (Fin n) k →* ℂˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → kˣ) :
    c (diagGL n (d ∘ σ)) = c (diagGL n d) := by sorry
