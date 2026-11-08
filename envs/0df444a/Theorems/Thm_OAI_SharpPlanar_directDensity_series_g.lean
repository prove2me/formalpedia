-- Prove2me | Theorems.Thm_OAI_SharpPlanar_directDensity_series_g
-- name    : OAI.SharpPlanar.directDensity_series_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-08T05:32:56.943197+00:00
-- url     : https://prove2.me/theorems/06ec6588-4254-45fe-98ae-e17807b56c77
-- title:
--   OAI.SharpPlanar.directDensity_series_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.directDensity_series` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open Set Filter MeasureTheory Asymptotics`, `open scoped Topology ContDiff SchwartzMap`, `open scoped SchwartzMap`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma directDensity_series_g (p : CardinalData) (ell : ℕ) (s : ℝ) :
--       (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
--         density p j t * directKernel ell s t).re =
--       p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
--         ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
--           p.x (n,true)*basisMoment true n.val ell s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.CardinalData` and `OAI.SharpPlanar.density` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.basisMoment` (definitions bundle `OAIQ098G1642` of this split); `OAI.SharpPlanar.directKernel` (definitions bundle `OAIQ098G1643` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.direct_spectral_bound_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exactLeft_origin_positive_g`, `OAI.SharpPlanar.exact_sign_tail_g`, `OAI.SharpPlanar.fullMoment_direct_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`, `OAI.SharpPlanar.tail_second_bound_g` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.directDensity_series)

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1643

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

open MeasureTheory
open scoped ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

namespace SharpPlanar
open MeasureTheory Set

lemma directDensity_series_g (p : CardinalData) (ell : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * directKernel ell s t).re =
    p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
      ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
        p.x (n,true)*basisMoment true n.val ell s) := by
  sorry

end SharpPlanar

end OAI
end
