-- Prove2me | Theorems.Thm_GlobalTheory_CharpolyDvd_charpoly_dvd_pow_finrank
-- name    : GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:07.000598+00:00
-- url     : https://prove2.me/theorems/c361ed7a-f432-4108-8cdd-ae309d36a711
-- title:
--   Charpoly Dvd: charpoly dvd pow finrank
-- statement:
--   The Charpoly Dvd construction uses the charpoly dvd pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZero.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZero.lean#L53-L67

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

theorem GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (G : K[X]) (hG : aeval f G = 0) :
    f.charpoly ∣ G ^ Module.finrank K V := by sorry
