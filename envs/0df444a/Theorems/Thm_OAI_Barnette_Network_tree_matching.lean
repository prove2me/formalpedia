-- Prove2me | Theorems.Thm_OAI_Barnette_Network_tree_matching
-- name    : OAI.Barnette.Network.tree_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:52:41.724375+00:00
-- url     : https://prove2.me/theorems/0c12c685-6612-4e3d-9319-7852e00d79b0
-- title:
--   A forest with black degrees two, and one at a root, contains a perfect matching
-- statement:
--   Let $N$ be a finite oriented network with vertex set $V$ and edge set $E$; every edge $e$ has a tail and a head, and $\operatorname{star}(v)$ denotes the set of edges having $v$ as tail or head. Let a set of *black* vertices be given such that every edge has exactly one black endpoint (the other vertices are *white*). Let $H\subseteq E$ be a set of edges whose boundary map $\partial_H:\mathbb{R}^H\to\mathbb{R}^V$, $(\partial_H x)(v)=\sum_{e\in H,\ \operatorname{head}(e)=v}x_e-\sum_{e\in H,\ \operatorname{tail}(e)=v}x_e$, is injective (so the edges of $H$ form a forest). Let $r$ be a black vertex, and assume
--
--   1. $|\operatorname{star}(v)\cap H|=1$ if $v=r$ and $|\operatorname{star}(v)\cap H|=2$ for every other black vertex $v$;
--   2. there are as many black vertices as white vertices.
--
--   Then $H$ contains a perfect matching of $N$:
--
--   $$\exists\,P\subseteq H\quad\text{such that}\quad |\operatorname{star}(v)\cap P|=1\ \text{ for every } v\in V.$$
--
--   No condition is imposed on the degrees of white vertices. The lemma is used to extract, from a spanning tree of a cubic bipartite graph obtained by deleting a removed edge set, a perfect matching whose complement turns out to be a Hamiltonian cycle.
--
--   **Formalization Note** The forest condition is `Function.Injective (N.restrict (Subtype.val : H → E)).boundary`; the colouring is a predicate `black` with `black (N.tail e) ↔ ¬black (N.head e)`, and the balance hypothesis compares the cardinalities of the subtypes of black and non-black vertices. The hypothesis that $r$ is black is part of the statement although the proof does not need it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ForestMatching.lean#L51-L148

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

theorem OAI.Barnette.Network.tree_matching (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (hi : Function.Injective (N.restrict (Subtype.val : H → E)).boundary)
    (root : V) (_hr : black root)
    (hd : ∀ v, black v → ((N.star v).filter (fun e => e ∈ H)).card = if v = root then 1 else 2)
    (hbal : Fintype.card {v // black v} = Fintype.card {v // ¬black v}) :
    ∃ P : Finset E, P ⊆ H ∧ ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1 := by sorry
