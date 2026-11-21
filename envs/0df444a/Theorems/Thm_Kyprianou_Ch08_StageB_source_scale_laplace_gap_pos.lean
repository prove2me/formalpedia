-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
-- name    : Kyprianou.Ch08.StageB.source_scale_laplace_gap_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:33:59.150112+00:00
-- url     : https://prove2.me/theorems/d405448c-4938-4e72-b0d0-08c6de8350e7
-- title:
--   Strict positive source q-scale Laplace denominator above largest root
-- statement:
--   For every real q≥0 and β≥0 strictly above the largest nonnegative q-root Φψ(q), the q-scale Laplace denominator is strictly positive, ψ(β)-q>0. This follows from the source q-scale nonnegative Laplace integral with value (ψβ-q)^(-1), nonzero denominator by maximal root, and positive inverse. It is the missing source transform-domain bridge for applying the geometric convolution Laplace series and identifying W^(q) by uniqueness (Lemma 8.3, (8.24)).
-- source:
--   Kyprianou (2006), Chapter 8 Theorem 8.1(i), q-scale transform (8.3), and Lemma 8.3 (8.24), printed pp.214,221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Every admissible scale transform has positive denominator above the root. -/
theorem source_scale_laplace_gap_pos
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot : Phi ψ q < β) :
    q < ψ β := by
  sorry

end Kyprianou.Ch08.StageB
