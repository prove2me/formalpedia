-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_choose_mul_norm_blockAverage_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:57.20114+00:00
-- url     : https://prove2.me/theorems/249265a7-93a0-417d-811e-50a5b8c990b3
-- title:
--   Binomial Partial Symmetrization Bound
-- statement:
--   This formalizes Lemma 2.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 2.2, p. 9, in orthogonal-representation form.
--
--   Let $\Omega$ be finite, let $V$ be a real inner-product space, and let $\rho$ be a permutation representation by linear isometries. Let $A,B,Q\subseteq\Omega$ and $d\in\mathbb N$ satisfy:
--   1. $|A|=d$ and $|B|=2d$.
--   2. $A$ and $B$ are disjoint.
--   3. $A\subseteq Q\subseteq A\cup B$.
--   4. $|Q|=2d$.
--   5. $v\in V$ is invariant under permutations fixing outside $A$ and under permutations fixing outside $B$.
--
--   Then
--
--   $$
--   \|v\|\le \binom{2d}{d}\,\|\operatorname{blockAverage}(\rho,Q,v)\|.
--   $$
--
--   This is the stronger binomial-factor version of the partial symmetrization estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L944-L1111 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage_408915f (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖ := by sorry
