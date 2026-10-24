-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_filter_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:56.831543+00:00
-- url     : https://prove2.me/theorems/0a9683fd-588b-40e3-a2d0-7cbe56bcfd33
-- title:
--   Squared Norm Expansion for Filtered Finite Sums
-- statement:
--   This is a finite-dimensional inner-product expansion.
--
--   Let $V$ be a real inner-product space, let $\mathcal E$ and $P$ be finite sets, let $r(F,E)$ be a decidable relation between $F\in P$ and $E\in\mathcal E$, and let $x_F\in V$. Then
--
--   $$
--   \sum_{E\in\mathcal E}\left\|\sum_{\substack{F\in P\\r(F,E)}}x_F\right\|^2
--   =
--   \sum_{F,F'\in P}
--   \#\{E\in\mathcal E:r(F,E)\land r(F',E)
--   \}\,\langle x_F,x_{F'}\rangle.
--   $$
--
--   This identity is a reusable way to expand sums of squared norms while retaining the multiplicity of common filters.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L220-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
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
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section SubsetSum
variable {α : Type*} [DecidableEq α]

theorem FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_408915f {β ι : Type*} (𝓔 : Finset β) (P : Finset ι) (r : ι → β → Prop)
    [∀ F E, Decidable (r F E)] (x : ι → V) :
    ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
      ∑ F ∈ P, ∑ F' ∈ P, ((𝓔.filter fun E => r F E ∧ r F' E).card : ℝ) * inner ℝ (x F) (x F') := by sorry
