-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedHensel_norm_sum_le_of_le
-- name    : GlobalTheory.UnramifiedHensel.norm_sum_le_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:38.329399+00:00
-- url     : https://prove2.me/theorems/44e9bf38-6db8-4f66-8805-edd0d696eab2
-- title:
--   Unramified Hensel: norm sum le of le
-- statement:
--   The Unramified Hensel construction uses the norm sum le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L96-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]

theorem GlobalTheory.UnramifiedHensel.norm_sum_le_of_le [Fintype ι] (a : ι → K) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, ‖a i‖ ≤ r) :
    ‖∑ i, a i‖ ≤ r := by sorry
