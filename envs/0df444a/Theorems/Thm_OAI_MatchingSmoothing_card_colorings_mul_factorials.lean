-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_card_colorings_mul_factorials
-- name    : OAI.MatchingSmoothing.card_colorings_mul_factorials
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:35:02.578417+00:00
-- url     : https://prove2.me/theorems/7da30372-22e9-4ad2-b140-c770542ec7e1
-- title:
--   Colourings with a prescribed colour histogram are counted by a multinomial coefficient
-- statement:
--   Let $\alpha$ be a finite set and $\beta$ a finite set of colours. The *histogram* of a colouring $f:\alpha\to\beta$ is the function $h_f:\beta\to\mathbb N$, $h_f(b)=|f^{-1}(b)|$, giving the number of points of each colour $b$. Let
--
--   $$
--   \mathrm{Col}(\alpha,h_f)=\{g:\alpha\to\beta\ :\ h_g=h_f\}
--   $$
--
--   be the set of colourings with the same histogram as $f$. Then
--
--   $$
--   |\mathrm{Col}(\alpha,h_f)|\cdot\prod_{b\in\beta}h_f(b)!\;=\;|\alpha|!\,.
--   $$
--
--   Equivalently, $|\mathrm{Col}(\alpha,h_f)|$ is the multinomial coefficient $\binom{|\alpha|}{(h_f(b))_{b\in\beta}}$. Identities of this kind convert averages of a quantity $F(f\circ\sigma)$ over uniformly random permutations $\sigma$ of $\alpha$ into averages of $F$ over the colourings with a fixed histogram. This is how the count is used in the later moment estimates for colourings of matchings.
--
--   **Formalization Note** The identity is an equality of natural numbers; $\mathrm{Col}(\alpha,h_f)$ is `Colorings α β (histogram f)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/ColoringCounts.lean#L67-L85

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8
variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

theorem OAI.MatchingSmoothing.card_colorings_mul_factorials [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) *
      (∏ b, (histogram f b).factorial) = (Fintype.card α).factorial := by sorry
