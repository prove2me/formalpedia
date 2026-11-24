-- Prove2me | Theorems.Thm_GlobalTheory_Lin_NonPrimeVonMangoldt_summable_nonPrime_vonMangoldt_div_rpow
-- name    : GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:24.811418+00:00
-- url     : https://prove2.me/theorems/9bd2bacf-f9c0-4776-b9e7-420684eb6744
-- title:
--   Non Prime Von Mangoldt: summable non Prime von Mangoldt div rpow
-- statement:
--   The Non Prime Von Mangoldt construction uses the summable non Prime von Mangoldt div rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean#L107-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean#L107-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.NonPrimeVonMangoldt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical

theorem GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by sorry
