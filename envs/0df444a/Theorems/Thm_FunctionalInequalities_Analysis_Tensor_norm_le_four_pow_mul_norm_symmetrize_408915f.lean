-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_four_pow_mul_norm_symmetrize_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_symmetrize_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:59.859137+00:00
-- url     : https://prove2.me/theorems/f8d1a22f-0f2b-4d3a-ab58-609b00590055
-- title:
--   Four-Power Coordinate Tensor Symmetrization Bound
-- statement:
--   This formalizes Lemma 2.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 2.2, p. 9.
--
--   Let $n,k,d\in\mathbb N$ with $3d\le k$, and let $A$ be a tensor in `Coord n k`, equivalently a real Hilbert–Schmidt tensor with $k$ index positions over $\operatorname{Fin}(n)$. Assume:
--   1. $A$ is invariant under permutations fixing every position outside the first $d$ slots.
--   2. $A$ is invariant under permutations fixing every position outside slots $d$ through $3d-1$.
--
--   Then
--
--   $$
--   \|A\|\le 4^d\,\|\operatorname{symmetrize}(n,k,2d,A)\|.
--   $$
--
--   The estimate leaves all positions after the first $3d$ untouched and allows $n=0$; the type itself does not require $d>0$.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 2.2, p. 9. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L85-L125 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coordinate`, declaration `FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_symmetrize`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_symmetrize_408915f {n k d : ℕ} (hk : 3 * d ≤ k) (A : Coord n k)
    (h₁ : ∀ σ ∈ fixingOutside (slots k 0 d), slotRep n k σ A = A)
    (h₂ : ∀ σ ∈ fixingOutside (slots k d (3 * d)), slotRep n k σ A = A) :
    ‖A‖ ≤ (4 : ℝ) ^ d * ‖symmetrize n k (2 * d) A‖ := by sorry
