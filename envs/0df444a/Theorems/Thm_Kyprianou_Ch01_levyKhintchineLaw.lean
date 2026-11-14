-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyKhintchineLaw
-- name    : Kyprianou.Ch01.levyKhintchineLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:16:48.225731+00:00
-- url     : https://prove2.me/theorems/256e77cc-f495-4800-bfdf-68efed2b94aa
-- title:
--   Theorem 1.3: Lévy–Khintchine characterisation of infinitely divisible real laws
-- statement:
--   Kyprianou (2006), Theorem 1.3, pp. 3–4. A real probability law has convolution roots of every positive integer order precisely when its characteristic function has a Lévy–Khintchine representation with an admissible Lévy triplet. LeanLevy uses the positive-sign exponent; this is the negative of Kyprianou's Ψ. This public chapter draft awaits compilation and independent source audit.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes with Applications (2006), Theorem 1.3, pp. 3–4; S. Link, LeanLevy, Lévy–Khintchine theorem statements, frozen GitHub source commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.levyKhintchineLaw
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ProbabilityTheory.IsInfinitelyDivisible μ ↔
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        ∀ (ξ : ℝ), charFun μ ξ = Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ) := by
  sorry
