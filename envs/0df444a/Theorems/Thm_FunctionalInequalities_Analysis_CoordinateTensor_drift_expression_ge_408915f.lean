-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_drift_expression_ge_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.drift_expression_ge_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:44.729824+00:00
-- url     : https://prove2.me/theorems/65787f7a-11b4-4124-a621-b11946cdc1bb
-- title:
--   Coordinate-Tensor Drift Lower Bound
-- statement:
--   This formalizes the algebraic part of Lemma 5.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 5.1, p. 22.
--
--   Let $n,r,m\in\mathbb N$ with $r+1=m$. Let $H_i$ be real $n\times n$ matrices such that:
--
--   1. Each $H_i$ is Hermitian.
--   2. For every $v\in\mathbb R^n$,
--      $$
--      \sum_i\|H_i v\|^2\le 8\|v\|^2.
--      $$
--
--   Let $T,L$ be order-$r$ coordinate tensors and let $W_i$ be a family of such tensors indexed by $i\in\operatorname{Fin}(n)$. Then
--
--   $$
--   \begin{aligned}
--   &\frac12\sum_i\|W_i\|^2-17m^2\|T\|^2-2\langle T,L\rangle\\
--   &\le -(m+1)\|T\|^2-2\langle T,L\rangle+\sum_i\|W_i\|^2
--   -2\sum_i\langle W_i,\Sigma_{H_i}T\rangle\\
--   &\quad+\frac12\sum_i\|\Sigma_{H_i}T\|^2
--   +\frac12\sum_i\sum_s\|H_i^{(s)}T\|^2.
--   \end{aligned}
--   $$
--
--   This is an algebraic drift lower bound; it does not assert the full probabilistic or analytic lemma from the paper.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 5.1, p. 22. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L174-L249 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.drift_expression_ge`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

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
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.drift_expression_ge_408915f {m : ℕ} (hm : r + 1 = m) (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i, (H i).IsHermitian)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T L : (Fin r → Fin n) → ℝ) (W : Fin n → (Fin r → Fin n) → ℝ) :
    (1 / 2 : ℝ) * ∑ i, inner (W i) (W i) - 17 * (m : ℝ) ^ 2 * inner T T - 2 * inner T L ≤
      -((m : ℝ) + 1) * inner T T - 2 * inner T L + ∑ i, inner (W i) (W i)
        - 2 * ∑ i, inner (W i) (actSum (H i) T)
        + (1 / 2 : ℝ) * ∑ i, inner (actSum (H i) T) (actSum (H i) T)
        + (1 / 2 : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by sorry
