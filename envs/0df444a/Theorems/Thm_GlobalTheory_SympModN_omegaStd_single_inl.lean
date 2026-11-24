-- Prove2me | Theorems.Thm_GlobalTheory_SympModN_omegaStd_single_inl
-- name    : GlobalTheory.SympModN.omegaStd_single_inl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:25:32.378924+00:00
-- url     : https://prove2.me/theorems/b6f86a52-b303-4b6e-ab33-3e50fdd91758
-- title:
--   Symp Mod N: omega Std single inl
-- statement:
--   The Symp Mod N construction uses the omega Std single inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticSimilitudeInvertibleModN.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticSimilitudeInvertibleModN.lean#L18-L20

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

theorem GlobalTheory.SympModN.omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inl i) 1) = -a (.inr i) := by sorry
