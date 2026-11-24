-- Prove2me | Theorems.Thm_GlobalTheory_CharpolyPowIrred_charpoly_dvd_pow_of_aeval
-- name    : GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:07.556537+00:00
-- url     : https://prove2.me/theorems/309c47ed-1d4e-4ab3-a3da-434317c683ea
-- title:
--   Charpoly Pow Irred: charpoly dvd pow of aeval
-- statement:
--   The Charpoly Pow Irred construction uses the charpoly dvd pow of aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharpolyEqPowOfIrreducible.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharpolyEqPowOfIrreducible.lean#L7-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyEqPowOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CharpolyPowIrred

theorem GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by sorry
