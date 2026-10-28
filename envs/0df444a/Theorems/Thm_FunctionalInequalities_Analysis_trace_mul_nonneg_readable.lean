-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_nonneg_readable
-- name    : FunctionalInequalities.Analysis.trace_mul_nonneg_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:41.481033+00:00
-- url     : https://prove2.me/theorems/8f84fe39-fbf6-4934-8c39-8242968c3544
-- title:
--   Nonnegative Trace Of A Product
-- statement:
--   This formalizes part of Theorem 2.5 of Letwin (arXiv:2607.24164v1), cited there as the key moment-map Hessian bound.
--
--   Let ι be a finite index type, and let A and C be real positive semidefinite matrices indexed by ι. Then the trace of their product is nonnegative:
--
--   $$0\leq \operatorname{tr}(AC).$$
--
--   The product AC itself is not asserted to be positive semidefinite.
--
--   This elementary trace-pairing fact is reusable whenever two positive semidefinite matrix fields produce a cross term.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem trace_mul_nonneg {ι : Type*} [Fintype ι]
--       {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
--       0 ≤ (A * C).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Previous: [`inverse_quadratic_young`](https://prove2.me/theorems/88b8a40a-52a8-4842-a7d8-a36165a50c94) · Next: [`traceGram_posSemidef`](https://prove2.me/theorems/244506ec-0037-4420-8e3c-8acdf6db2119).
--
--   [Source excerpt, lines 366–368](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L366-L368) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L364-L382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.trace_mul_nonneg`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

theorem FunctionalInequalities.Analysis.trace_mul_nonneg_readable {ι : Type*} [Fintype ι]
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    0 ≤ (A * C).trace := by sorry
