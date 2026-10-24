-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_scalar_log_gap_408915f
-- name    : FunctionalInequalities.Analysis.scalar_log_gap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:44.0144+00:00
-- url     : https://prove2.me/theorems/3faebff9-1700-41f9-b64c-d57047572ea9
-- title:
--   Scalar Quantitative Logarithm Concavity
-- statement:
--   This private lemma is a scalar inequality underlying a matrix log-determinant estimate.
--
--   For positive real numbers $a,b$ and an upper bound $K$ satisfying $a\le K$ and $b\le K$,
--
--   $$\log b+\frac{(b-a)^2}{2K^2}\le \log a+\frac{b-a}{a}.$$
--
--   The declaration `scalar_log_gap` is a technical one-variable estimate. The hypotheses imply in particular that $K>0$, although positivity of $K$ is not listed separately.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L150-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.LogDet`, declaration `_private.FunctionalInequalities.Analysis.Matrix.LogDet.0.FunctionalInequalities.Analysis.scalar_log_gap`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LogDetConcavity

lemma FunctionalInequalities.Analysis.scalar_log_gap_408915f {a b K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haK : a ≤ K) (hbK : b ≤ K) :
    Real.log b + (b - a) ^ 2 / (2 * K ^ 2) ≤
      Real.log a + (b - a) / a := by sorry
