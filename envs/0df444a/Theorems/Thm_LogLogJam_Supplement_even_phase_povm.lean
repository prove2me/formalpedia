-- Prove2me | Theorems.Thm_LogLogJam_Supplement_even_phase_povm
-- name    : LogLogJam.Supplement.even_phase_povm
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:25:14.410427+00:00
-- url     : https://prove2.me/theorems/ead13720-1e0c-40a9-b5c6-e0b02ac0c7e7
-- title:
--   A full Fock POVM realizing the even canonical phase measurement
-- statement:
--   There is a normalized positive operator-valued measure with real outcomes on the one-mode Fock space whose compression to even photon numbers has the canonical phase matrix elements from Eq. (146). For an event $B$ and occupations $2k,2l$ the matrix element is the integral of $e^{i(k-l)\alpha}/(2\pi)$ over $B\cap[0,2\pi)$.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — Definition 8.17, Eqs. (146)–(147)

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw
import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Classical ComplexConjugate

namespace LogLogJam.Supplement

theorem even_phase_povm :
    ∃ M : FockPOVM (Occupation (Fin 1)) ℝ,
      ∀ B : Set ℝ, MeasurableSet B → ∀ k l : ℕ,
      M.effect B (fun _ => 2*k) (fun _ => 2*l) =
        (∫ α in B ∩ Set.Ico 0 (2 * Real.pi),
          Complex.exp (Complex.I * (((k : ℝ) - l) * α))) / (2 * Real.pi : ℝ) := by sorry

end LogLogJam.Supplement
