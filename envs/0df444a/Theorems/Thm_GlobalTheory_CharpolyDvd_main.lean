-- Prove2me | Theorems.Thm_GlobalTheory_CharpolyDvd_main
-- name    : GlobalTheory.CharpolyDvd.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:28.909682+00:00
-- url     : https://prove2.me/theorems/d3091246-6b1c-4bbd-b7b3-934343f024f8
-- title:
--   Charpoly Dvd: main
-- statement:
--   The Charpoly Dvd construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZero.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyDvdPowFinrankOfAevalEqZero.lean#L69-L71

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

theorem GlobalTheory.CharpolyDvd.main : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V := by sorry
