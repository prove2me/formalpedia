-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_scalar_log_gap_readable
-- name    : FunctionalInequalities.Analysis.scalar_log_gap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:17.826648+00:00
-- url     : https://prove2.me/theorems/048f38d9-1535-47f8-a190-2a68f7a7a501
-- title:
--   Scalar Quantitative Logarithm Concavity
-- statement:
--   This lemma is a scalar inequality underlying a matrix log-determinant estimate.
--
--   For positive real numbers $a,b$ and an upper bound $K$ satisfying $a\le K$ and $b\le K$,
--
--   $$\log b+\frac{(b-a)^2}{2K^2}\le \log a+\frac{b-a}{a}.$$
--
--   The declaration `scalar_log_gap_readable` is a technical one-variable estimate. The hypotheses imply in particular that $K>0$, although positivity of $K$ is not listed separately.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma scalar_log_gap {a b K : ℝ}
--       (ha : 0 < a) (hb : 0 < b) (haK : a ≤ K) (hbK : b ≤ K) :
--       Real.log b + (b - a) ^ 2 / (2 * K ^ 2) ≤
--         Real.log a + (b - a) / a
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/LogDet`](https://prove2.me/theorems/4063692a-a203-477a-8815-ef391dc73f51).
--
--   Previous: [`forall_posDef_add_log_det_le_trace_iff`](https://prove2.me/theorems/99f67c0b-fea3-4671-8e5b-e62a896aa733) · Next: [`log_det_add_frobenius_sq_le`](https://prove2.me/theorems/42e7e2e1-c8f2-4cb8-b154-81b11d6da306).
--
--   [Source excerpt, lines 150–153](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L150-L153) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L150-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.LogDet`, declaration `_private.FunctionalInequalities.Analysis.Matrix.LogDet.0.FunctionalInequalities.Analysis.scalar_log_gap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet

lemma FunctionalInequalities.Analysis.scalar_log_gap_readable {a b K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haK : a ≤ K) (hbK : b ≤ K) :
    Real.log b + (b - a) ^ 2 / (2 * K ^ 2) ≤
      Real.log a + (b - a) / a := by sorry
