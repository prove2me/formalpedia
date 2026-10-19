-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_monomial_candidate_identity
-- name    : OAI.MatchingSmoothing.monomial_candidate_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:52:08.909978+00:00
-- url     : https://prove2.me/theorems/7cfb5b41-ca85-4551-a8a1-81d57b6e2d78
-- title:
--   On matchings extending a partial matching, candidate-edge counts equal color-pair counts minus a constant
-- statement:
--   Let $V$ be a finite set, $C$ a set of colors and $z:V\to C$ a coloring. Represent the perfect matchings of $V$ as fixed-point-free involutions $M:V\to V$, and for an ordered pair $e=(u,w)$ let $x_e(M)=1$ if $M(u)=w$ and $0$ otherwise. For a finite list $l$ of ordered pairs let $x_l$ be the product of the $x_e$ over the entries of $l$ (the edge monomial, i.e. the indicator that $M(u)=w$ for every pair $(u,w)$ of $l$), and let $U=\operatorname{supp}(l)$ be the set of all coordinates of pairs in $l$. For a color pair $c=(c_1,c_2)\in C\times C$ define the *table coordinate*
--
--   $$
--   T_c(M)=\big|\{v\in V:\ z(v)=c_1,\ z(M(v))=c_2\}\big|
--   $$
--
--   and the set of *candidate edges* $\mathrm{Cand}=\{(u,w)\in V\times V:\ u\notin U,\ w\notin U,\ u\neq w,\ z(u)=c_1,\ z(w)=c_2\}$. Let $M_0$ be a perfect matching that contains $l$ (that is, $M_0(u)=w$ for every pair $(u,w)$ of $l$), and let $s=\big|\{v\in U:\ z(v)=c_1,\ z(M_0(v))=c_2\}\big|$. Then, as functions on the perfect matchings of $V$,
--
--   $$
--   x_l\cdot\sum_{e\in\mathrm{Cand}}x_e\;=\;x_l\cdot\big(T_c-s\big),
--   $$
--
--   where $s$ denotes the constant function with value $s$.
--
--   On the matchings that extend the partial matching $l$, the number of vertices $v$ outside $\operatorname{supp}(l)$ with $z(v)=c_1$ and $z(M(v))=c_2$ is thus the global count $T_c$ minus a correction that is the same for all such matchings. This identity drives a recurrence expressing the color-symmetrized version of an edge monomial with $m+1$ factors as an affine function of the table coordinates times the symmetrized monomial with $m$ factors.
--
--   **Formalization Note** $T_c$ is `tableCoordinate z c`, $\mathrm{Cand}$ is `candidateEdges z (Pairing.edgeSupport l) c`, $x_l$ is `Pairing.edgeMonomial l`, and the constant appears as `s • 1`. No finiteness or decidability is assumed for the color type `C`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PartialColorings.lean#L122-L142

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

open OAI OAI.MatchingSmoothing
universe u_1 u_2
attribute [local instance] Classical.propDecidable
variable {V : Type u_1} {C : Type u_2} [Fintype V]

theorem OAI.MatchingSmoothing.monomial_candidate_identity (z : V → C) (l : List (V × V)) (c : C × C)
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    Pairing.edgeMonomial l * (∑ e ∈ candidateEdges z (Pairing.edgeSupport l) c,
      Pairing.edgeCoord e) =
    Pairing.edgeMonomial l * (tableCoordinate z c -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = c.1 ∧ z (M₀.1 v) = c.2 then (1:ℝ) else 0) • 1) := by sorry
