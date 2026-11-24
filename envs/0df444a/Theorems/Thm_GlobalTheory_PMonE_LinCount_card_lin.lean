-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LinCount_card_lin
-- name    : GlobalTheory.PMonE.LinCount.card_lin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:38:44.15026+00:00
-- url     : https://prove2.me/theorems/5fdf1200-fcc8-4ab4-aa48-e5ffa7e89380
-- title:
--   Lin Count: card lin
-- statement:
--   The Lin Count construction uses the card lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L119-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L119-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

theorem GlobalTheory.PMonE.LinCount.card_lin (q K E : ℕ) (M : ℕ → Matrix m m F) :
    Nat.card {x : m → F // Integral x ∧ gsum q (K + (E + 1)) M x = 0} =
      Nat.card {X : Fin (K + 1) × m → F // Integral X ∧ gsum q (E + 1) (lin K M) X = 0} := by sorry
