-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_Pairing_lowDegree_invariant
-- name    : OAI.MatchingSmoothing.Pairing.lowDegree_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:44:30.188976+00:00
-- url     : https://prove2.me/theorems/c17fb6bb-299f-4ec3-817d-7a9a40773816
-- title:
--   Low-degree edge polynomials on perfect matchings are closed under relabelling of the vertices
-- statement:
--   Let $V$ be a set and let $\mathcal M(V)$ be the set of perfect matchings of $V$, encoded as fixed-point-free involutions $M:V\to V$ (so $M(v)$ is the partner of $v$). A permutation $p$ of $V$ relabels a matching as $p\cdot M=pMp^{-1}$, the matching whose edges are the pairs $\{p(u),p(v)\}$ for the edges $\{u,v\}$ of $M$, and it acts on real functions $f:\mathcal M(V)\to\mathbb R$ by
--
--   $$
--   (p\cdot f)(M)=f(p^{-1}Mp).
--   $$
--
--   For an ordered pair $e=(u,v)\in V\times V$ let $x_e:\mathcal M(V)\to\mathbb R$ be the edge indicator, $x_e(M)=1$ if $M(u)=v$ and $x_e(M)=0$ otherwise. For $d\in\mathbb N$ let $\mathcal P_d$ be the real linear span of all products $x_{e_1}x_{e_2}\cdots x_{e_m}$ with $m\le d$ (repetitions allowed, the empty product being the constant function $1$); these are the polynomials of degree at most $d$ in the edge indicators.
--
--   **Theorem.** For every permutation $p$ of $V$, every $d\in\mathbb N$ and every $f\in\mathcal P_d$,
--
--   $$
--   p\cdot f\in\mathcal P_d .
--   $$
--
--   Thus every $\mathcal P_d$ is a subrepresentation of the action of the symmetric group of $V$ on functions of perfect matchings. Since relabelling permutes the coordinates of $\mathbb R^{\mathcal M(V)}$, for finite $V$ the orthogonal complement of $\mathcal P_d$ is then invariant as well, and the orthogonal projection onto $\mathcal P_d$ commutes with relabelling. These facts underlie the representation-theoretic dimension and multiplicity arguments on the high-degree part of the space of functions on matchings.
--
--   **Formalization Note** $\mathcal P_d$ is `lowDegree edgeCoord d`, the span of the products `(l.map edgeCoord).prod` over lists `l` of length at most `d`, and $p\cdot f$ is `Pairing.act p f`, defined by `f (relabel p⁻¹ M)`. The vertex type `V` is arbitrary; no finiteness is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EquivariantCompression.lean#L24-L44

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

open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing
universe u_1 u_2 u_3
variable {V : Type u_1}

theorem OAI.MatchingSmoothing.Pairing.lowDegree_invariant (p : Equiv.Perm V) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree edgeCoord d) :
    act p f ∈ lowDegree edgeCoord d := by sorry
