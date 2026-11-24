-- Prove2me | Theorems.Thm_GlobalTheory_ZeroBand_norm_term_le
-- name    : GlobalTheory.ZeroBand.norm_term_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:03:20.552849+00:00
-- url     : https://prove2.me/theorems/aa41a56f-9e7a-4f0b-9df1-906de1fb98dd
-- title:
--   Zero Band: norm term le
-- statement:
--   The Zero Band construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteBox.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteBox.lean#L21-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteBox
import Theorems.Thm_GlobalTheory_LLeft_norm_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroBand

theorem GlobalTheory.ZeroBand.norm_term_le (m : ℕ) {u T : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) {ρ : ℂ} (h1 : ρ.re < 1)
    (h2 : T ≤ |ρ.im|) : ‖(m : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (m : ℝ) * (u / T) := by sorry
