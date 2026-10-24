-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_letwin_trace_weighted_slices_408915f
-- name    : FunctionalInequalities.Analysis.letwin_trace_weighted_slices_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:51.074056+00:00
-- url     : https://prove2.me/theorems/56f69840-8330-4bcf-a510-0e44515fded6
-- title:
--   Weighted Matrix-Slice Trace Expansion
-- statement:
--   This is a private finite matrix expansion identity.
--
--   For real $n\times n$ matrices $P,A,C$ and a family of matrices $V_a$, one has
--
--   $$
--   \sum_k\operatorname{tr}\left(A\left(\sum_aP_{ka}V_a\right)C\left(\sum_bP_{kb}V_b\right)\right)
--   =
--   \sum_{a,b}(P^{\mathsf T}P)_{ab}\operatorname{tr}(AV_aCV_b).
--   $$
--
--   The statement is purely algebraic and is used to rewrite a sum of traces of weighted matrix slices.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L243-L290 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Energy`, declaration `_private.FunctionalInequalities.Analysis.Matrix.Trace.Energy.0.FunctionalInequalities.Analysis.letwin_trace_weighted_slices`; the repository is private at upload time).

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TensorComparison

lemma FunctionalInequalities.Analysis.letwin_trace_weighted_slices_408915f {n : ℕ}
    (P A C : Matrix (Fin n) (Fin n) ℝ)
    (V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ k, (A * (∑ a, P k a • V a) * C *
      (∑ b, P k b • V b)).trace) =
      ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace := by sorry
