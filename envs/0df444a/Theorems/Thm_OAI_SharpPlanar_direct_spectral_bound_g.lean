-- Prove2me | Theorems.Thm_OAI_SharpPlanar_direct_spectral_bound_g
-- name    : OAI.SharpPlanar.direct_spectral_bound_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:37:47.896033+00:00
-- url     : https://prove2.me/theorems/9f660866-af4c-4cd7-a1f7-561893ffb82e
-- title:
--   OAI.SharpPlanar.direct_spectral_bound_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.direct_spectral_bound` of [lean/OAI/Analysis/PlanarPacking/Envelopes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Envelopes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerBasis`, `open scoped BigOperators`):
--
--   ```lean
--   lemma direct_spectral_bound_g (p : CardinalData) (ell : ℕ) (s : ℝ) :
--       |cardinalSeries p ell s| ≤
--         |p.C| *25*Real.pi^ell+(|p.c₀|+|p.d₀|+‖p.x‖)*directEnvelope ell
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.CardinalData` and `OAI.SharpPlanar.X` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.cardinalSeries` (definitions bundle `OAIQ098G1642` of this split); `OAI.SharpPlanar.directEnvelope` (definitions bundle `OAIQ098G1675` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.halfSign_0_N1_right_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`, `OAI.SharpPlanar.table_jet_sharp_g` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Envelopes.lean (declaration OAI.SharpPlanar.direct_spectral_bound)

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1675

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma direct_spectral_bound_g (p : CardinalData) (ell : ℕ) (s : ℝ) :
    |cardinalSeries p ell s| ≤
      |p.C| *25*Real.pi^ell+(|p.c₀|+|p.d₀|+‖p.x‖)*directEnvelope ell := by
  sorry
end SharpPlanar

end OAI
end
