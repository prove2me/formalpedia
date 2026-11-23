-- Prove2me | Theorems.Thm_GlobalTheory_CharpolyDvd_matrix_charpoly_dvd_pow
-- name    : GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:01.216554+00:00
-- url     : https://prove2.me/theorems/fbcb218e-1bc5-4220-a048-745079c7aeb7
-- title:
--   Charpoly Dvd: matrix charpoly dvd pow
-- statement:
--   The Charpoly Dvd construction uses the matrix charpoly dvd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZero.lean#L6-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZero.lean#L6-L51

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.CharpolyDvd

theorem GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by sorry
