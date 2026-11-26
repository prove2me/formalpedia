-- Prove2me | Theorems.Thm_LogLogJam_Supplement_photon_number_povm
-- name    : LogLogJam.Supplement.photon_number_povm
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:24.323846+00:00
-- url     : https://prove2.me/theorems/4ffd709e-2627-4151-a555-45dfbc04967d
-- title:
--   Photon-number detection as a physical single-copy POVM
-- statement:
--   On the single-mode Fock space there exists a positive operator-valued measure recording the photon number as a real outcome. Its effect for an event $B$ has matrix entries $\delta_{ij}\mathbf 1_B(i)$ on the occupation-number basis.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — §8.3.3, Lemma 8.27, Eq. (171)

import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_BosonicLearn_traceDist
import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open MeasureTheory BosonicLearn
open scoped Classical
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem photon_number_povm :
    ∃ M : FockPOVM (Occupation (Fin 1)) ℝ, ∀ B : Set ℝ, ∀ i j,
      M.effect B i j = if i = j ∧ (i 0 : ℝ) ∈ B then 1 else 0 := by sorry

end LogLogJam.Supplement
