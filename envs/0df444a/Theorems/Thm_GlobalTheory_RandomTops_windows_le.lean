-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_windows_le
-- name    : GlobalTheory.RandomTops.windows_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:18.227726+00:00
-- url     : https://prove2.me/theorems/0fa43101-7151-49d5-99a4-7c3c5b31e193
-- title:
--   Random Tops: windows le
-- statement:
--   The Random Tops construction uses the windows le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L261-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L261-L299

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}

theorem GlobalTheory.RandomTops.windows_le (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (n i₀ L K K' : ℕ) (hK : K' ≤ K) (b : ℝ)
    (hb : ∀ A : Finset ℕ, A.card ≤ L → ex δ A (fun T => ind (K' ≤ T.card)) ≤ b) :
    ex δ ((Finset.range n).erase i₀)
      (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K)) ≤ n * b := by sorry
