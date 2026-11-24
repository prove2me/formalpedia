-- Prove2me | Theorems.Thm_GlobalTheory_SympModN_omegaStd_nsmul_left
-- name    : GlobalTheory.SympModN.omegaStd_nsmul_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:25:26.744878+00:00
-- url     : https://prove2.me/theorems/712f9bca-0065-432d-89aa-f7be6dce5e6c
-- title:
--   Symp Mod N: omega Std nsmul left
-- statement:
--   The Symp Mod N construction uses the omega Std nsmul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticSimilitudeInvertibleModN.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticSimilitudeInvertibleModN.lean#L6-L12

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticSimilitudeInvertibleModN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SympModN

theorem GlobalTheory.SympModN.omegaStd_nsmul_left {h : ℕ} (N : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (N • a) b = N * omegaStd a b := by sorry
