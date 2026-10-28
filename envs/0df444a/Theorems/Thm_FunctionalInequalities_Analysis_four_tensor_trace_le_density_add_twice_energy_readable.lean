-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_four_tensor_trace_le_density_add_twice_energy_readable
-- name    : FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:45.32623+00:00
-- url     : https://prove2.me/theorems/da9d02bd-cdb4-4359-adcc-5a3ee2a58b5b
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem four_tensor_trace_le_density_add_twice_energy {n : ℕ}
--       (B H W : Matrix (Fin n) (Fin n) ℝ)
--       (hB : B.PosSemidef) (hH : H.PosDef) (hW : W.PosSemidef)
--       (T : Fin n → Fin n → Fin n → ℝ)
--       (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b) :
--       let Tm := fun i => Matrix.of fun a b => T i a b
--       let G := Matrix.of fun i j => (H⁻¹ * Tm i * H⁻¹ * Tm j).trace
--       let D := ∑ i : Fin n, ∑ j : Fin n, H⁻¹ i j * (B * Tm i * B * Tm j).trace
--       0 ≤ D ∧ 4 * D ≤
--         (2 * (B * H * B * (-H + H * W * H + G)).trace + 2 * D) +
--           2 * (B * H * B * H).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/TraceGram`](https://prove2.me/theorems/d77e66c8-d9dd-4a0b-bdab-7928904ca310).
--
--   Supporting theorems: [`letwin_tensor_comparison_trace_gram`](https://prove2.me/theorems/ca7beff0-2f64-408f-99c9-add2cbb214d3), [`traceGram_posSemidef`](https://prove2.me/theorems/244506ec-0037-4420-8e3c-8acdf6db2119), [`trace_mul_nonneg`](https://prove2.me/theorems/8f84fe39-fbf6-4934-8c39-8242968c3544).
--
--   Previous: [`letwin_tensor_comparison_trace_gram`](https://prove2.me/theorems/ca7beff0-2f64-408f-99c9-add2cbb214d3).
--
--   [Source excerpt, lines 89–99](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/TraceGram.lean#L89-L99) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/TraceGram.lean#L86-L127 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.TraceGram`, declaration `FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_TraceGram

theorem FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy_readable {n : ℕ}
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
