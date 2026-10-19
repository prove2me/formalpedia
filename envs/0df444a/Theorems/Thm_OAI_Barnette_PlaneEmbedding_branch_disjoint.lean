-- Prove2me | Theorems.Thm_OAI_Barnette_PlaneEmbedding_branch_disjoint
-- name    : OAI.Barnette.PlaneEmbedding.branch_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:08:15.494004+00:00
-- url     : https://prove2.me/theorems/e3f2d230-27b2-4181-9b31-43f61cc3a4f1
-- title:
--   Branches of distinct vertices in a plane embedding are disjoint
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$. A *plane embedding* of $G$ consists of an injective map $P:V\to\mathbb{R}^2$ and, for every ordered pair $(v,w)$ of adjacent vertices, an injective continuous path $\gamma_{vw}:[0,1]\to\mathbb{R}^2$ with $\gamma_{vw}(0)=P(v)$ and $\gamma_{vw}(1)=P(w)$, such that (i) $\gamma_{wv}(t)=\gamma_{vw}(1-t)$; (ii) $\gamma_{vw}(t)=P(z)$ only if $t=0$ and $z=v$, or $t=1$ and $z=w$; (iii) if $\gamma_{vw}(t)=\gamma_{xy}(s)$ with $t,s\in(0,1)$, then $(x,y)=(v,w)$ or $(x,y)=(w,v)$. A *dart* is an ordered pair $d=(v,w)$ of adjacent vertices, with $\gamma_d=\gamma_{vw}$. The *branch* of a vertex $v$ is the vertex point together with the first thirds of all arcs leaving $v$,
--   $$\operatorname{Br}(v)=\{P(v)\}\cup\bigcup_{w\ \text{adjacent to}\ v}\gamma_{vw}\bigl([0,\tfrac13]\bigr).$$
--
--   **Theorem.** Fix a plane embedding of $G$. For any two distinct vertices $v\neq w$,
--
--   $$
--   \operatorname{Br}(v)\cap\operatorname{Br}(w)=\varnothing .
--   $$
--
--   No finiteness of $V$ is needed. Branches are small connected neighbourhoods of the vertices inside the drawing; their pairwise disjointness is one of the separation properties that survive thickening and discretization by square cells, and so produce disjoint connected vertex sets in the square grid representing the vertices of $G$.
--
--   **Formalization Note** The embedding is `E : PlaneEmbedding G` with fields `point` and `arc`; darts are Mathlib's `G.Dart`, the arc of a dart is `E.curve d`, and the branch is `E.branch v`, with the parameter $\tfrac13$ as an element of `unitInterval`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Traces.lean#L103-L125

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces

open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding
variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

theorem OAI.Barnette.PlaneEmbedding.branch_disjoint {v w : V} (hvw : v ≠ w) :
    Disjoint (E.branch v) (E.branch w) := by sorry
