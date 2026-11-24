-- Prove2me | Theorems.Thm_GlobalTheory_SympModN_exists_eq_nsmul_iff
-- name    : GlobalTheory.SympModN.exists_eq_nsmul_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:09.789589+00:00
-- url     : https://prove2.me/theorems/c6198609-62f9-42e3-bef7-f3eb8d74a775
-- title:
--   Symp Mod N: exists eq nsmul iff
-- statement:
--   The Symp Mod N construction uses the exists eq nsmul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticSimilitudeInvertibleModN.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticSimilitudeInvertibleModN.lean#L32-L39

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

theorem GlobalTheory.SympModN.exists_eq_nsmul_iff {ι : Type*} (N : ℕ) (hN : N ≠ 0) (a : ι → ℤ) :
    (∃ b, a = N • b) ↔ ∀ j, (N : ℤ) ∣ a j := by sorry
