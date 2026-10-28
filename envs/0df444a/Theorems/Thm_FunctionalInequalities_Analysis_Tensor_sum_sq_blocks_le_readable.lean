-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_sq_blocks_le_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:12.568183+00:00
-- url     : https://prove2.me/theorems/4c57808a-480e-483b-b687-b1b06f6ba0cf
-- title:
--   Disjoint Copy-Block Square-Sum Bound
-- statement:
--   This is a finite-dimensional Hilbert–Schmidt counting estimate, corresponding to the disjoint-copy-block estimate used after (112) in Bizeul–Klartag–Lehec, Proposition 7.1.
--
--   Let $\iota$ and $\kappa$ be finite types, let $d>0$, and let
--
--   $$
--   A:(\operatorname{Fin}(d)\to\operatorname{Option}(\kappa\times\iota))\to\mathbb R.
--   $$
--
--   Then the entries indexed by the disjoint blocks $(i,j)$ form a subfamily of all entries, and therefore
--
--   $$
--   \sum_{i\in\kappa}\sum_{j:\operatorname{Fin}(d)\to\iota}
--   A\bigl(k\mapsto \operatorname{some}(i,j(k))\bigr)^2
--   \le
--   \sum_{J:\operatorname{Fin}(d)\to\operatorname{Option}(\kappa\times\iota)}A(J)^2.
--   $$
--
--   The statement is a technical injectivity-and-counting lemma for block decompositions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_sq_blocks_le
--       {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) :
--       ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 ≤ ∑ J, A J ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f).
--
--   Previous: [`norm_le_four_pow_mul_norm_symmetrize`](https://prove2.me/theorems/f0e3d670-24f7-4ef8-927b-cc5e41de1898).
--
--   [Source excerpt, lines 153–155](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L153-L155) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L151-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coordinate`, declaration `FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le_readable
    {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) :
    ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 ≤ ∑ J, A J ^ 2 := by sorry
