-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_pairWeight_overlap_square_moment
-- name    : OAI.MatchingSmoothing.pairWeight_overlap_square_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:37:15.676099+00:00
-- url     : https://prove2.me/theorems/38a4529c-e10b-42a1-a33a-390d0f8cb603
-- title:
--   Second moment of pair-weight overlaps under a random permutation
-- statement:
--   Let $H$ and $C$ be finite sets and $V=H\times\{0,1\}$. For a real $C\times C$ matrix $A$ and a colouring $f:V\to C$, let $w_A(f)=\prod_{i\in H}A_{f(i,0),f(i,1)}$ be its pair weight. Suppose $A$ is symmetric, has nonnegative entries, and fixes a vector with positive entries: $Av=v$ for some $v\in\mathbb R^C$ with $v_c>0$ for all $c$. Then
--
--   $$
--   \sum_{\sigma\in\mathrm{Sym}(V)}\Big(\sum_{f:V\to C}w_A(f)\,w_A(f\circ\sigma)\Big)^2\ \le\ |\mathrm{Sym}(V)|\cdot(|H|+1)^{|C|^2}.
--   $$
--
--   The inner sum is an $A$-weighted correlation between the standard matching $\{\{(i,0),(i,1)\}\}$ and its image under $\sigma$. The theorem says that its mean square over a uniformly random $\sigma$ is at most $(|H|+1)^{|C|^2}$, which is polynomial in $|H|$ for a fixed number of colours. Symmetric nonnegative matrices with a positive fixed vector arise by normalising the symmetric joint distribution of the colours at the two ends of an edge. This is how the bound is applied to colour tables of matchings.
--
--   **Formalization Note** Symmetry is stated as `A.IsHermitian`, which for real matrices means $A^{\mathsf T}=A$. In the Lean expression for the right-hand side, `^` is right-associative, so the exponent is $|C|^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TensorBounds.lean#L113-L132

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

theorem OAI.MatchingSmoothing.pairWeight_overlap_square_moment (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    (∑ σ : Equiv.Perm (H × Bool),
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ (Fintype.card C) ^ 2 := by sorry
