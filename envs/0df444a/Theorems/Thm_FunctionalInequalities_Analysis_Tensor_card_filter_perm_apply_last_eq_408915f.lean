-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_filter_perm_apply_last_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:24.716977+00:00
-- url     : https://prove2.me/theorems/46c3a644-e95a-4603-8685-fd528243443c
-- title:
--   Permutation Fiber Cardinality
-- statement:
--   This statement counts permutations with a prescribed image of the last index.
--
--   For $d\in\mathbb N$ and $k\in\operatorname{Fin}(d+1)$, consider permutations $\sigma$ of $\operatorname{Fin}(d+1)$ satisfying $\sigma(\operatorname{last}(d))=k$. Their number is exactly $d!$:
--
--   $$
--   \#\{\sigma\in\operatorname{Sym}(\operatorname{Fin}(d+1)):\sigma(\operatorname{last}(d))=k\}=d!.
--   $$
--
--   This is a finite combinatorial identity used to group permutation sums according to the value of their last argument.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L84-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, declaration `FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fintype.Perm

noncomputable section
open scoped RealInnerProductSpace
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq_408915f {d : ℕ} (k : Fin (d + 1)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d) = k).card =
      d.factorial := by sorry
