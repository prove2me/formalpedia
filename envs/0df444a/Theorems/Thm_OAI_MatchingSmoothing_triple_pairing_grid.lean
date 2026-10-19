-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_triple_pairing_grid
-- name    : OAI.MatchingSmoothing.triple_pairing_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:04:42.651768+00:00
-- url     : https://prove2.me/theorems/f21a0ea9-f55b-4c4e-9303-8ba200d28d87
-- title:
--   A scaled cubic grid of crossing profiles is realized by perfect matchings of a three-colored set
-- statement:
--   Let $s\in\mathbb{N}$ and let $V_s=A\sqcup B\sqcup C$ be the three-colored set consisting of a set $A$ of $2s+1$ vertices of color $0$, a set $B$ of $2s+1$ vertices of color $1$ and a set $C$ of $2s$ vertices of color $2$, so $|V_s|=6s+2$. For a perfect matching $M$ of $V_s$ (a fixed-point-free involution of $V_s$) its *cross vector* is
--   $$X(M)=\bigl(e_M(A,B),\,e_M(A,C),\,e_M(B,C)\bigr)\in\mathbb{R}^3,$$
--   where $e_M(P,Q)$ is the number of edges of $M$ with one endpoint in $P$ and the other in $Q$.
--
--   **Theorem.** Let $s,l,d\in\mathbb{N}$ satisfy $2ld\le s$. Then for every $k=(k_0,k_1,k_2)\in\{0,1,\dots,d\}^3$ there is a perfect matching $M$ of $V_s$ with
--   $$X(M)=\bigl(1+2lk_0,\ 2lk_1,\ 2lk_2\bigr).$$
--
--   The realized points form the grid $x_0+2l\,\{0,\dots,d\}^3$ around the base point $x_0=(1,0,0)$ with step $2l$. Together with the five special profiles $(1,0,0),(0,1,1),(3,0,0),(1,2,0),(1,0,2)$, which are realized by a companion lemma, they are the sample points at which a degree-$d$ polynomial in the crossing counts is interpolated in the PSD-rank lower bound for perfect matchings. The condition $2ld\le s$ ensures that the color classes are large enough to carry all requested crossing edges.
--
--   **Formalization Note** The vertex type is `TripleVertices s = (Fin (2s+1) ⊕ Fin (2s+1)) ⊕ (Fin s × Bool)` with the coloring `tripleColor`, the index $k$ is a function `Fin 3 → Fin (d+1)`, and the cross vector is `crossVector tripleColor M`. No lower bound on $s$ is assumed beyond $2ld\le s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/AdmissiblePoints.lean#L29-L50

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

theorem OAI.MatchingSmoothing.triple_pairing_grid {s l d : ℕ} (hs : 2*l*d ≤ s) (k : Fin 3 → Fin (d+1)) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (fun a => (![1,0,0] a : ℝ) + (2*l:ℝ)*(k a:ℝ)) := by sorry
