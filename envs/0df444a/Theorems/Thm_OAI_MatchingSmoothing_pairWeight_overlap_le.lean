-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_pairWeight_overlap_le
-- name    : OAI.MatchingSmoothing.pairWeight_overlap_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:36:14.197449+00:00
-- url     : https://prove2.me/theorems/b8c6b1f0-839d-440c-8688-d638ffb84656
-- title:
--   Pair-weight overlaps of a symmetric matrix with spectrum in $[-1,1]$ are at most a colouring count
-- statement:
--   Let $H$ and $C$ be finite sets and $V=H\times\{0,1\}$. Call a colouring $f:V\to C$ *pair-constant* if $f(i,0)=f(i,1)$ for all $i\in H$. For a real $C\times C$ matrix $A$, the *pair weight* of a colouring $f:V\to C$ is
--
--   $$
--   w_A(f)=\prod_{i\in H}A_{f(i,0),\,f(i,1)} .
--   $$
--
--   Let $U$ be a real orthogonal $C\times C$ matrix ($U^{\mathsf T}U=I$), let $d\in\mathbb R^C$ with $|d_c|\le1$ for all $c$, and put $A=U\operatorname{diag}(d)\,U^{\mathsf T}$. Then for every permutation $\sigma$ of $V$,
--
--   $$
--   \sum_{f:V\to C}w_A(f)\,w_A(f\circ\sigma)\ \le\ \#\{f:V\to C\ :\ f\text{ and }f\circ\sigma\text{ are both pair-constant}\}.
--   $$
--
--   By the spectral theorem, the matrices $A$ of this form are exactly the real symmetric matrices with all eigenvalues in $[-1,1]$. The theorem bounds a weighted correlation between the standard matching $\{\{(i,0),(i,1)\}\}$ and its image under $\sigma$ by a purely combinatorial quantity: the number of colourings that are constant on the edges of both matchings. Summing over $\sigma$, this count is controlled on average by the colouring moment bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TransitionMatrices.lean#L123-L147

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3
open Matrix
variable {V : Type u_1} {C : Type u_2} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
variable {H : Type u_3} [Fintype H] [DecidableEq H]

theorem OAI.MatchingSmoothing.pairWeight_overlap_le (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (hd : ∀ c, |d c| ≤ 1)
    (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) ≤
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by sorry
