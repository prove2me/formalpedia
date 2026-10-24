-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_letwin_tensor_trace_identity_408915f
-- name    : FunctionalInequalities.Analysis.letwin_tensor_trace_identity_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:50.716857+00:00
-- url     : https://prove2.me/theorems/3c2c5860-01f0-45bb-b259-632b1062a0fe
-- title:
--   Tensor Trace Expansion Identity
-- statement:
--   This is a private finite-dimensional tensor trace identity.
--
--   Let $G,M$ be real $n\times n$ matrices with $M^{\mathsf T}=M$, and let $T_{abc}$ satisfy symmetry in its last two indices, $T_{abc}=T_{acb}$. Then
--
--   $$
--   \sum_{a,c}G_{ac}\operatorname{tr}(MT_aGT_c)
--   =
--   \sum_{i,j}M_{ij}\sum_{a,b,c,d}G_{ac}G_{bd}T_{abi}T_{cdj},
--   $$
--
--   where $(T_a)_{ij}=T_{aij}$. This private identity expands the trace expression into coordinate sums for the tensor comparison argument.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L318-L391 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Energy`, declaration `_private.FunctionalInequalities.Analysis.Matrix.Trace.Energy.0.FunctionalInequalities.Analysis.letwin_tensor_trace_identity`; the repository is private at upload time).

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

lemma FunctionalInequalities.Analysis.letwin_tensor_trace_identity_408915f {n : ℕ}
    (G M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ a b c, T a b c = T a c b) :
    (∑ a, ∑ c, G a c *
      (M * Matrix.of (fun i j => T a i j) * G *
        Matrix.of (fun i j => T c i j)).trace) =
      ∑ i, ∑ j, M i j *
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by sorry
