-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_slots_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.card_slots_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:04.974816+00:00
-- url     : https://prove2.me/theorems/20da986d-ba34-4ddb-8dcb-3728fea08846
-- title:
--   Cardinality of an Index Interval
-- statement:
--   This is an elementary cardinality identity for coordinate slots.
--
--   For natural numbers $a,b,k$ with $b\le k$, let `slots k a b` be the positions $p\in\operatorname{Fin}(k)$ satisfying $a\le p<b$. Then
--
--   $$
--   |\operatorname{slots}(k,a,b)|=b-a.
--   $$
--
--   The result is used to verify the sizes of the coordinate blocks in the tensor symmetrization theorem.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L64-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coordinate`, declaration `FunctionalInequalities.Analysis.Tensor.card_slots`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.card_slots_408915f {k a b : ℕ} (hb : b ≤ k) : (slots k a b).card = b - a := by sorry
