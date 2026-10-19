-- Prove2me | Theorems.Thm_OAI_Barnette_Network_independent_edges_bound
-- name    : OAI.Barnette.Network.independent_edges_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:50:40.552013+00:00
-- url     : https://prove2.me/theorems/fc754405-992b-426b-bef3-379973bedf8b
-- title:
--   A forest has at most $|U|-1$ edges inside a nonempty vertex set $U$
-- statement:
--   Let $N$ be a finite oriented network with vertex set $V$ and edge set $E$, every edge $e$ having a tail $\operatorname{tail}(e)$ and a head $\operatorname{head}(e)$. Let $\partial_N:\mathbb{R}^E\to\mathbb{R}^V$, $(\partial_N x)(v)=\sum_{\operatorname{head}(e)=v}x_e-\sum_{\operatorname{tail}(e)=v}x_e$, be its boundary map, and suppose $\partial_N$ is injective; this says that $N$ carries no nonzero circulation, i.e. $N$ is a forest without loops or parallel edges. Let $S\subseteq E$ and let $U\subseteq V$ be a nonempty set such that every edge of $S$ has both its tail and its head in $U$. Then
--
--   $$|S|+1\le|U|.$$
--
--   This is the familiar bound that a forest on $n\ge1$ vertices has at most $n-1$ edges, stated for the edges of $S$ inside $U$ and with the forest condition expressed through the boundary map. It supplies the Hall-type inequality used to extract perfect matchings from forests.
--
--   **Formalization Note** The hypothesis is `Function.Injective N.boundary`, where `N.boundary` is the linear map given by the signed incidence matrix; $S$ and $U$ are `Finset`s.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Matching.lean#L183-L214

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

theorem OAI.Barnette.Network.independent_edges_bound (hi : Function.Injective N.boundary)
    (S : Finset E) (U : Finset V) (hne : U.Nonempty)
    (hU : ∀ e ∈ S, N.tail e ∈ U ∧ N.head e ∈ U) : S.card + 1 ≤ U.card := by sorry
