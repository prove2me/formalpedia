-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_cellAverage_star
-- name    : OAI.MatchingSmoothing.cellAverage_star
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:07:24.559262+00:00
-- url     : https://prove2.me/theorems/215687b4-2bb7-464d-bf1e-abc87fc1b54b
-- title:
--   Cell averages at crossing profile $(x,0,0)$ split into independent core and cell matchings
-- statement:
--   Let $A$, $B$, $C$ and $I$ be finite sets; $I$ indexes *cells*, each a copy of $C$. Write $\mathcal P(X)$ for the set of perfect matchings (fixed-point-free involutions) of a finite set $X$. The *global* vertex set is $W=(A\sqcup B)\sqcup(I\times C)$, and the *local* vertex set is $W_{\mathrm{loc}}=(A\sqcup B)\sqcup C$, colored $0$ on $A$, $1$ on $B$ and $2$ on $C$. For a perfect matching $L$ of $W_{\mathrm{loc}}$ let $X(L)\in\mathbb{R}^3$ be its cross vector: the numbers of edges of $L$ joining colors $0$–$1$, $0$–$2$ and $1$–$2$. For $M\in\mathcal P(A\sqcup B)$ and a family $N=(N_j)_{j\in I}$ of matchings of $C$, let $M\oplus N\in\mathcal P(W)$ act as $M$ on $A\sqcup B$ and as $N_j$ on the cell $\{j\}\times C$.
--
--   Fix $f\colon\mathcal P(W)\to\mathbb{R}$ and a cell $i\in I$. The *extension average* of a local matching $L$ is
--   $$\mathcal E_if(L)=\mathbb{E}_{(N_j)_{j\neq i}}\,f\bigl(L\oplus(N_j)_{j\neq i}\bigr).$$
--   Here $L$ is placed on $(A\sqcup B)\sqcup(\{i\}\times C)$, and the $N_j$, $j\neq i$, are independent uniformly random matchings of $C$ placed on the other cells. The *cell average* at $x\in\mathbb{R}^3$ is the mean of $\mathcal E_if(L)$ over all local matchings $L$ with $X(L)=x$, and it is $0$ if there is no such $L$.
--
--   **Theorem.** For every $i\in I$, every $f$ and every real $x$,
--   $$\operatorname{avg}_{L\in\mathcal P(W_{\mathrm{loc}}):\,X(L)=(x,0,0)}\ \mathcal E_if(L)\;=\;\mathbb{E}_{M\in\mathcal M_x}\ \mathbb{E}_{N\in\mathcal P(C)^I}\ f(M\oplus N).$$
--   Here $\mathcal M_x$ is the set of perfect matchings of $A\sqcup B$ with exactly $x$ edges between $A$ and $B$, both expectations are uniform, and an expectation over an empty set is $0$.
--
--   At a crossing profile with no edges touching the color-2 cell, a local matching is just a matching of the core $A\sqcup B$ together with an independent matching of the cell. The cell average therefore becomes a plain product average over core matchings with $x$ cross edges and over independent matchings of all cells. As a consequence its value at $(x,0,0)$ does not depend on the cell $i$. This is used to evaluate cell-averaged matrices at the star point of the interpolation scheme.
--
--   **Formalization Note** The cell average is `cellAverage i f x`, defined as `predicateAverage` of `extensionAverage i f` over local pairings with `crossVector threeColor L = x`. The placement of the local matching is `extendLocal`, a transport along an explicit bijection $(A\sqcup B)\sqcup C\sqcup(\{j\neq i\}\times C)\to(A\sqcup B)\sqcup(I\times C)$, and $M\oplus N$ is `Pairing.sum M (Pairing.cellwise N)`. The condition defining $\mathcal M_x$ is `tableCoordinate abColor (0,1) M = x`, which counts the vertices of $A$ whose partner lies in $B$. The expectation $\mathbb{E}$ is `Finset.expect`, which is $0$ over an empty type, so the identity holds for every real $x$; when $x$ is not an attainable count both sides vanish.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CellAverages.lean#L32-L60

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

theorem OAI.MatchingSmoothing.cellAverage_star (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (x : ℝ) :
    cellAverage i f ![x,0,0] =
      𝔼 M : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x},
        𝔼 N : I → Pairing C, f (Pairing.sum M.1 (Pairing.cellwise N)) := by sorry
