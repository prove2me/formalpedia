-- Prove2me | Theorems.Thm_LogLogJam_Supplement_nonadaptive_transcript_product
-- name    : LogLogJam.Supplement.nonadaptive_transcript_product
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:20:48.932177+00:00
-- url     : https://prove2.me/theorems/fa312ac9-b82d-53bc-a302-41335c706928
-- title:
--   Product law for fixed single-copy POVMs on fresh identical states
-- statement:
--   For an arbitrary finite sequence of history-independent Fock POVMs on fresh copies of a density operator, the full BosonicLearn transcript law equals the finite product of the one-copy Born laws. The coordinate laws may differ between rounds. This includes the empty transcript.
-- source:
--   https://arxiv.org/abs/2607.12983, §8.3, individual samples from the two fixed readouts; reuse of BosonicLearn.transcriptLaw.

import Definitions.Def_BosonicLearn_transcriptLaw
open MeasureTheory ProbabilityTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement
theorem nonadaptive_transcript_product {n N : ℕ} {O : Type} [MeasurableSpace O] [Inhabited O]
    (S : AdaptiveScheme n N O) (ρ : State (Occupation (Fin n)))
    (h : ∀ (i : Fin N) (x y : Fin i → O), S.povm i x = S.povm i y) :
    transcriptLaw S ρ.coefficients = Measure.pi (fun i => (S.povm i (fun _ => default)).law ρ.coefficients) := by sorry
end LogLogJam.Supplement
