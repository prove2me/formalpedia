-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_fixingOutside_eq_smul_sum_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:57.226746+00:00
-- url     : https://prove2.me/theorems/b365ac6d-6d3a-4414-98af-a3aaaed82f8b
-- title:
--   Grouping Supported Permutation Sums by Block Images
-- statement:
--   This is a block-sum identity used in partial symmetrization.
--
--   Let $\Omega$ be finite, let $V$ be a real inner-product space, and let $\rho$ be a permutation representation by linear isometries. Let $A,B,Q\subseteq\Omega$ satisfy $A\subseteq Q\subseteq A\cup B$. For $v\in V$ and a function $T$ on finite subsets, assume that for every permutation $\sigma$ fixing outside $A\cup B$,
--
--   $$
--   \rho(\sigma)v=T(\sigma(A)).
--   $$
--
--   Then
--
--   $$
--   \sum_{\sigma\text{ fixing outside }Q}\rho(\sigma)v
--   =\frac{\#\{\sigma\text{ fixing outside }Q\}}{\binom{|Q|}{|A|}}
--   \sum_{\substack{F\subseteq Q\\|F|=|A|}}T(F).
--   $$
--
--   The identity converts a permutation sum into a sum over subsets, with the common fiber size accounted for by the scalar factor.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L806-L905 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum_408915f (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B Q : Finset Ω}
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (v : V) (T : Finset Ω → V)
    (hT : ∀ σ ∈ fixingOutside (A ∪ B), ρ σ v = T (A.image σ)) :
    ∑ σ ∈ fixingOutside Q, ρ σ v =
      (((fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
        ∑ F ∈ Q.powersetCard A.card, T F := by sorry
