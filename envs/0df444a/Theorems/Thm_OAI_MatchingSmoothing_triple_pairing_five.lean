-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_triple_pairing_five
-- name    : OAI.MatchingSmoothing.triple_pairing_five
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:03:28.001676+00:00
-- url     : https://prove2.me/theorems/0c2ccb0b-e77f-4143-8219-e5f9154c6c94
-- title:
--   Five prescribed crossing profiles are realized by perfect matchings of a three-colored set
-- statement:
--   Let $s\in\mathbb{N}$ and let $V_s=A\sqcup B\sqcup C$ be the three-colored set consisting of a set $A$ of $2s+1$ vertices of color $0$, a set $B$ of $2s+1$ vertices of color $1$ and a set $C$ of $2s$ vertices of color $2$, so $|V_s|=6s+2$. For a perfect matching $M$ of $V_s$ (a fixed-point-free involution of $V_s$) its *cross vector* is
--   $$X(M)=\bigl(e_M(A,B),\,e_M(A,C),\,e_M(B,C)\bigr)\in\mathbb{R}^3,$$
--   where $e_M(P,Q)$ is the number of edges of $M$ with one endpoint in $P$ and the other in $Q$.
--
--   **Theorem.** If $s\ge1$, then for each of the five vectors
--   $$(1,0,0),\qquad(0,1,1),\qquad(3,0,0),\qquad(1,2,0),\qquad(1,0,2)$$
--   there is a perfect matching $M$ of $V_s$ whose cross vector $X(M)$ equals that vector.
--
--   With $x_0=(1,0,0)$ these five points are $x_0$, $x_0+(-1,1,1)$, $x_0+(2,0,0)$, $x_0+(0,2,0)$ and $x_0+(0,0,2)$, the points that enter the second-order finite difference used in the interpolation step of the PSD-rank lower bound for perfect matchings. The lemma guarantees that each of these crossing profiles is attained by an actual matching, so that averages over the matchings with a given profile are taken over nonempty sets there.
--
--   **Formalization Note** The vertex type is `TripleVertices s = (Fin (2s+1) ⊕ Fin (2s+1)) ⊕ (Fin s × Bool)` with the coloring `tripleColor`, and the five vectors are listed by an index `j : Fin 5`. The cross vector is `crossVector tripleColor M`. Its coordinate for the color pair $(a,b)$ counts the vertices of color $a$ whose partner has color $b$, which is the number of $a$–$b$ edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/AdmissiblePoints.lean#L9-L27

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables

open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.MatchingSmoothing.triple_pairing_five {s : ℕ} (hs : 1 ≤ s) (j : Fin 5) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Fin 3 → ℝ) := by sorry
