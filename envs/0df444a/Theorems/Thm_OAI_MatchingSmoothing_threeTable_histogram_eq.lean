-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_threeTable_histogram_eq
-- name    : OAI.MatchingSmoothing.threeTable_histogram_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:38:24.172218+00:00
-- url     : https://prove2.me/theorems/efff7612-ab0d-4824-939a-7a61181df2f9
-- title:
--   The pair-type table of a 3-colouring determines its colour histogram
-- statement:
--   Let $H$ be a nonempty finite set and $V=H\times\{0,1\}$, with standard pairs $\{(i,0),(i,1)\}$. For a $3$-colouring $f:V\to\{0,1,2\}$, its *table* $T_f$ counts the standard pairs of each type: for each of the six unordered colour pairs $\{a,b\}$ ($a=b$ allowed), $T_f(\{a,b\})$ is the number of $i\in H$ with $\{f(i,0),f(i,1)\}=\{a,b\}$. Let $h_f(a)$ be the number of vertices of colour $a$. If two colourings $f,g:V\to\{0,1,2\}$ have the same table, then they have the same colour histogram:
--
--   $$
--   T_f=T_g\quad\Longrightarrow\quad h_f(a)=h_g(a)\quad\text{for }a=0,1,2 .
--   $$
--
--   Consequently, every colouring with the same table as a reference colouring $f_0$ also has the same colour counts as $f_0$. So the class of colourings with a given table sits inside a single class of colourings with prescribed colour counts, and both classes can be handled on the same set of colourings.
--
--   **Formalization Note** The Lean statement carries the hypothesis $0<|H|$. For empty $H$ the conclusion would hold trivially, since $V$ is then empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean#L229-L242

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10
open Matrix
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem OAI.MatchingSmoothing.threeTable_histogram_eq {f g : H × Bool → Fin 3} (hH : 0 < Fintype.card H)
    (h : threeTable f = threeTable g) : histogram f = histogram g := by sorry
