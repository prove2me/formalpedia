-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table
-- name    : OAI.MatchingSmoothing.standardPairing_table
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:41:26.592129+00:00
-- url     : https://prove2.me/theorems/ebb2ea15-e4fd-4404-8403-428038f116e0
-- title:
--   The edge-type table of the standard matching is the pair-type table of the colouring
-- statement:
--   Let $V$ be a finite set and $f:V\to\{0,1,2\}$ a $3$-colouring. For a perfect matching $M$ of $V$, viewed as a fixed-point-free involution with $M(v)$ the partner of $v$, define the *edge-type table* of $M$ under $f$ for each of the six unordered colour pairs $t=\{a,b\}$ by
--
--   $$
--   \mathrm{tab}_M(f)(t)=\Big\lfloor\tfrac12\,\#\{v\in V:\ \{f(v),f(M(v))\}=t\}\Big\rfloor .
--   $$
--
--   Each edge is seen from both of its endpoints, so this is the number of edges of $M$ whose endpoint colours form the type $t$. Now let $V=H\times\{0,1\}$ for a finite set $H$, and let $M_0$ be the standard matching $(i,0)\leftrightarrow(i,1)$, with edges $\{(i,0),(i,1)\}$. Let $T_f(t)=\#\{i\in H:\ \{f(i,0),f(i,1)\}=t\}$ be the pair-type table of $f$. Then
--
--   $$
--   \mathrm{tab}_{M_0}(f)=T_f .
--   $$
--
--   So the table of a general matching under a colouring extends the table defined via the standard pairs. Combined with the relabelling rule $\mathrm{tab}_{pMp^{-1}}(f)=\mathrm{tab}_M(f\circ p)$, it identifies the table of the matching $pM_0p^{-1}$ under $f$ with $T_{f\circ p}$. This translates conditions on colourings of arbitrary matchings into conditions on permuted colourings of the standard matching.
--
--   **Formalization Note** The halving is natural-number division by $2$; here it is exact, because the count is even. The second coordinate is `Bool`, and $M_0$ is `standardPairing`, which applies `Equiv.boolNot` to it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean#L48-L70

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3
variable {H : Type u_2} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem OAI.MatchingSmoothing.standardPairing_table (f : H × Bool → Fin 3) :
    (standardPairing (H := H)).table f = threeTable f := by sorry
