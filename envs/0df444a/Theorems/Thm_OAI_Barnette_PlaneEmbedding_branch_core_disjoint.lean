-- Prove2me | Theorems.Thm_OAI_Barnette_PlaneEmbedding_branch_core_disjoint
-- name    : OAI.Barnette.PlaneEmbedding.branch_core_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:10:39.949466+00:00
-- url     : https://prove2.me/theorems/883f8c0b-4209-497c-a671-a69cda727642
-- title:
--   In a plane embedding the branch of a vertex misses the middle third of every non-incident edge
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$. A *plane embedding* of $G$ consists of an injective map $P:V\to\mathbb{R}^2$ and, for every ordered pair $(v,w)$ of adjacent vertices, an injective continuous path $\gamma_{vw}:[0,1]\to\mathbb{R}^2$ with $\gamma_{vw}(0)=P(v)$ and $\gamma_{vw}(1)=P(w)$, such that (i) $\gamma_{wv}(t)=\gamma_{vw}(1-t)$; (ii) $\gamma_{vw}(t)=P(z)$ only if $t=0$ and $z=v$, or $t=1$ and $z=w$; (iii) if $\gamma_{vw}(t)=\gamma_{xy}(s)$ with $t,s\in(0,1)$, then $(x,y)=(v,w)$ or $(x,y)=(w,v)$. A *dart* is an ordered pair $d=(v,w)$ of adjacent vertices, with $\gamma_d=\gamma_{vw}$. The *branch* of a vertex $v$ is the vertex point together with the first thirds of all arcs leaving $v$,
--   $$\operatorname{Br}(v)=\{P(v)\}\cup\bigcup_{w\ \text{adjacent to}\ v}\gamma_{vw}\bigl([0,\tfrac13]\bigr).$$
--   The *core* of a dart $d$ is the middle third of its arc, $\operatorname{Co}(d)=\gamma_d\bigl([\tfrac13,\tfrac23]\bigr)$.
--
--   **Theorem.** Fix a plane embedding of $G$, a dart $d=(a,b)$ and a vertex $v$ with $v\neq a$ and $v\neq b$. Then
--
--   $$
--   \operatorname{Br}(v)\cap\operatorname{Co}(d)=\varnothing .
--   $$
--
--   Together with disjointness of branches of distinct vertices and of cores of distinct edges, this says that two of these pieces of a plane drawing can meet only if they are the branch of a vertex and the core of an edge at that vertex, or cores of the same edge. After thickening and passing to square cells, it yields the condition that a vertex's grid region avoids the corridors of edges not incident with it.
--
--   **Formalization Note** The embedding is `E : PlaneEmbedding G`; darts are Mathlib's `G.Dart` with endpoints `d.fst` and `d.snd`, the branch is `E.branch v` and the core is `E.core d`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Traces.lean#L156-L179

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

theorem OAI.Barnette.PlaneEmbedding.branch_core_disjoint {v : V} {e : G.Dart}
    (hv₁ : v ≠ e.fst) (hv₂ : v ≠ e.snd) : Disjoint (E.branch v) (E.core e) := by sorry
