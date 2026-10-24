-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_four_tensor_trace_le_density_add_twice_energy_408915f
-- name    : FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:54.763979+00:00
-- url     : https://prove2.me/theorems/bd452326-5e09-4a19-bc25-842fe0d97d67
-- title:
--   Four-Tensor Trace Energy Comparison
-- statement:
--   This formalizes a finite-dimensional trace-energy comparison used in Theorem 2.5 of Letwin (arXiv:2607.24164v1), cited there as the key moment-map Hessian bound.
--
--   Let n be a natural number. Let B and W be real positive semidefinite n-by-n matrices, let H be positive definite, and let T(a,b,c) be a real three-tensor satisfying
--
--   1. T(a,b,c)=T(b,a,c) for all a,b,c;
--   2. T(a,b,c)=T(a,c,b) for all a,b,c.
--
--   For Tᵢ with entries T(i,a,b), define
--
--   $$D=\sum_{i,j}(H^{-1})_{ij}\operatorname{tr}(B T_i B T_j),$$
--
--   and let G be the matrix with entries $G_{ij}=\operatorname{tr}(H^{-1}T_iH^{-1}T_j)$. Then
--
--   $$0\leq D,$$
--
--   and
--
--   $$4D\leq 2\operatorname{tr}\!\bigl(BHB(-H+HWH+G)\bigr)+2D+2\operatorname{tr}(BHBH).$$
--
--   This is a technical pointwise comparison for the tensor energy and weak trace density, valid in every finite dimension, including the possibility that B is singular.
--
--   **Formalization Note** Matrix inverse is the Lean inverse of the positive-definite matrix H, and all sums and traces are over `Fin n`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/TraceGram.lean#L86-L127 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.TraceGram`, declaration `FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

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

theorem FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy_408915f {n : ℕ}
    (B H W : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (hH : H.PosDef) (hW : W.PosSemidef)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b) :
    let Tm := fun i => Matrix.of fun a b => T i a b
    let G := Matrix.of fun i j => (H⁻¹ * Tm i * H⁻¹ * Tm j).trace
    let D := ∑ i : Fin n, ∑ j : Fin n, H⁻¹ i j * (B * Tm i * B * Tm j).trace
    0 ≤ D ∧ 4 * D ≤
      (2 * (B * H * B * (-H + H * W * H + G)).trace + 2 * D) +
        2 * (B * H * B * H).trace := by sorry
