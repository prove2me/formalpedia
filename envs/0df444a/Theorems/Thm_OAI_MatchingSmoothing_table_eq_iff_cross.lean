-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_table_eq_iff_cross
-- name    : OAI.MatchingSmoothing.table_eq_iff_cross
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:00:58.485426+00:00
-- url     : https://prove2.me/theorems/f8b16ca8-c72d-4f13-bef7-119ac51cb888
-- title:
--   The color table of a perfect matching is determined by its three bichromatic edge counts
-- statement:
--   Let $H$ be a finite set and $V=H\times\{0,1\}$, and represent the perfect matchings of $V$ as fixed-point-free involutions $M$ of $V$. Fix a coloring $z:V\to\{0,1,2\}$. For a color pair $c=(a,b)$ let
--
--   $$
--   T_{(a,b)}(M)=\big|\{v\in V:\ z(v)=a,\ z(M(v))=b\}\big|,
--   $$
--
--   and define the cross vector $X(M)=\big(T_{(0,1)}(M),\,T_{(0,2)}(M),\,T_{(1,2)}(M)\big)\in\mathbb R^3$. The color table $\operatorname{tab}_z(M)$ records, for each of the six unordered color pairs $\{a,b\}$ ($a=b$ allowed), the number of edges of $M$ whose endpoints have colors $a$ and $b$. Then for all perfect matchings $M,N$ of $V$,
--
--   $$
--   \operatorname{tab}_z(M)=\operatorname{tab}_z(N)\iff X(M)=X(N).
--   $$
--
--   For $a\neq b$ the number $T_{(a,b)}(M)$ is exactly the number of edges of $M$ with one endpoint of color $a$ and one of color $b$, so $X(M)$ lists the three bichromatic entries of the table. The theorem says that, for a fixed coloring, the three monochromatic entries are then determined as well, because the color-class sizes are fixed. Consequently the color-table classes of matchings are exactly the level sets of $X$, and functions of the table can be treated as functions of three real variables.
--
--   **Formalization Note** $X(M)$ is `crossVector z M`, built from `tableCoordinate z (a,b)` for the pairs listed in `crossPair`, and the table is `Pairing.table`. Note that $T_{(a,a)}(M)$ counts each monochromatic edge twice, once from each endpoint.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TableGeometry.lean#L42-L62

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
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.MatchingSmoothing.table_eq_iff_cross {H : Type u_4} [Fintype H] [DecidableEq H]
    (z : H × Bool → Fin 3) (M N : Pairing (H × Bool)) :
    M.table z = N.table z ↔ crossVector z M = crossVector z N := by sorry
