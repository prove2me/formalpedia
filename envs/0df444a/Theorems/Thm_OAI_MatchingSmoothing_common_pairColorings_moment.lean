-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_common_pairColorings_moment
-- name    : OAI.MatchingSmoothing.common_pairColorings_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:35:37.471778+00:00
-- url     : https://prove2.me/theorems/0e455f12-093e-4456-b41f-9aa283606086
-- title:
--   Average count of colourings constant on both the standard matching and its image under a random permutation
-- statement:
--   Let $H$ be a finite set and $V=H\times\{0,1\}$, a set of $2|H|$ vertices grouped into the standard pairs $\{(i,0),(i,1)\}$, $i\in H$. Let $\beta$ be a finite set of colours. Call a colouring $f:V\to\beta$ *pair-constant* if $f(i,0)=f(i,1)$ for every $i\in H$. For a permutation $\sigma$ of $V$, the colouring $f\circ\sigma$ is pair-constant exactly when $f$ is constant on each of the pairs $\{\sigma(i,0),\sigma(i,1)\}$, the edges of the image of the standard matching under $\sigma$. Let
--
--   $$
--   N_\beta(\sigma)=\#\{f:V\to\beta\ :\ f\text{ and }f\circ\sigma\text{ are both pair-constant}\}.
--   $$
--
--   Then
--
--   $$
--   \sum_{\sigma\in\mathrm{Sym}(V)}N_\beta(\sigma)\ \le\ |\mathrm{Sym}(V)|\cdot(|H|+1)^{|\beta|}.
--   $$
--
--   Equivalently, for a uniformly random permutation $\sigma$ of $V$ the expected value of $N_\beta(\sigma)$ is at most $(|H|+1)^{|\beta|}$. For $\sigma=\mathrm{id}$ all $|\beta|^{|H|}$ pair-constant colourings are counted. The theorem says that for a typical $\sigma$ the count is only polynomial in $|H|$ when the number of colours is fixed. Applied with the colour set $C\times C$, this bound controls second moments of overlaps of pair weights over random permutations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/ColoringCounts.lean#L306-L336

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8
variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]
variable {H : Type u_5} [Fintype H] [DecidableEq H]

theorem OAI.MatchingSmoothing.common_pairColorings_moment [Fintype β] :
    (∑ σ : Equiv.Perm (H × Bool),
      (Fintype.card {f : H × Bool → β // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ)) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ Fintype.card β := by sorry
