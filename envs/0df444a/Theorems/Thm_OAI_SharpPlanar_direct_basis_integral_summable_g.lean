-- Prove2me | Theorems.Thm_OAI_SharpPlanar_direct_basis_integral_summable_g
-- name    : OAI.SharpPlanar.direct_basis_integral_summable_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T19:25:11.765795+00:00
-- url     : https://prove2.me/theorems/b1acd6bc-d4c4-47b4-a8bd-a424d1a8fc39
-- title:
--   OAI.SharpPlanar.direct_basis_integral_summable_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.direct_basis_integral_summable` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma direct_basis_integral_summable_g (x : X) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
--       Summable (fun n : Node => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
--         ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.X`, `OAI.SharpPlanar.u` and `OAI.SharpPlanar.v` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.directKernel` (definitions bundle `OAIQ098G1643` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.direct_positive_series_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.direct_basis_integral_summable)

import Mathlib
import Definitions.Def_OAIQ098G001
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

namespace SharpPlanar
open MeasureTheory Set

lemma direct_basis_integral_summable_g (x : X) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    Summable (fun n : Node => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t) := by
  sorry

end SharpPlanar

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

end OAI
end
