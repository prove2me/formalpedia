-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_sq_blocks_le_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:01.418995+00:00
-- url     : https://prove2.me/theorems/24f7001d-108d-4016-992e-5064a5146427
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L151-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coordinate`, declaration `FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
section FiniteIndex
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le_408915f
    {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) :
    ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 ≤ ∑ J, A J ^ 2 := by sorry
