-- Prove2me | Theorems.Thm_GlobalTheory_T_charpoly_dvd_pow_finrank_of_aeval_eq_zero
-- name    : GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:28.705799+00:00
-- url     : https://prove2.me/theorems/5b2a49e0-3fde-47a7-ad1b-2c0474fe86f0
-- title:
--   T: charpoly dvd pow finrank of aeval eq zero
-- statement:
--   The T construction uses the charpoly dvd pow finrank of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZeroStatement.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZeroStatement.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V := by sorry
