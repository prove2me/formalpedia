-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_letwin_tensor_trace_identity_readable
-- name    : FunctionalInequalities.Analysis.letwin_tensor_trace_identity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:57.275249+00:00
-- url     : https://prove2.me/theorems/fae84bdf-a098-4054-b01e-b2eb219e86ec
-- title:
--   Tensor Trace Expansion Identity
-- statement:
--   This is a finite-dimensional tensor trace identity.
--
--   Let $G,M$ be real $n\times n$ matrices with $M^{\mathsf T}=M$, and let $T_{abc}$ satisfy symmetry in its last two indices, $T_{abc}=T_{acb}$. Then
--
--   $$
--   \sum_{a,c}G_{ac}\operatorname{tr}(MT_aGT_c)
--   =
--   \sum_{i,j}M_{ij}\sum_{a,b,c,d}G_{ac}G_{bd}T_{abi}T_{cdj},
--   $$
--
--   where $(T_a)_{ij}=T_{aij}$. This identity expands the trace expression into coordinate sums for the tensor comparison argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma letwin_tensor_trace_identity {n : ℕ}
--       (G M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
--       (T : Fin n → Fin n → Fin n → ℝ)
--       (hT : ∀ a b c, T a b c = T a c b) :
--       (∑ a, ∑ c, G a c *
--         (M * Matrix.of (fun i j => T a i j) * G *
--           Matrix.of (fun i j => T c i j)).trace) =
--         ∑ i, ∑ j, M i j *
--           ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Energy`](https://prove2.me/theorems/3c755a85-5be5-4a52-9826-3a9afe9620f8).
--
--   Previous: [`letwin_trace_weighted_slices`](https://prove2.me/theorems/a517441b-78a2-4418-90ee-2e5a6b365cc7) · Next: [`letwin_tensor_comparison`](https://prove2.me/theorems/6e239757-a405-483f-bb98-9824d874a734).
--
--   [Source excerpt, lines 318–326](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L318-L326) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L318-L391 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Energy`, declaration `_private.FunctionalInequalities.Analysis.Matrix.Trace.Energy.0.FunctionalInequalities.Analysis.letwin_tensor_trace_identity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy

open Matrix

lemma FunctionalInequalities.Analysis.letwin_tensor_trace_identity_readable {n : ℕ}
    (G M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ a b c, T a b c = T a c b) :
    (∑ a, ∑ c, G a c *
      (M * Matrix.of (fun i j => T a i j) * G *
        Matrix.of (fun i j => T c i j)).trace) =
      ∑ i, ∑ j, M i j *
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by sorry
