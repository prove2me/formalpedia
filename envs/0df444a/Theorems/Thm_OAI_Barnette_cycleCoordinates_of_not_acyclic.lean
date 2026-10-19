-- Prove2me | Theorems.Thm_OAI_Barnette_cycleCoordinates_of_not_acyclic
-- name    : OAI.Barnette.cycleCoordinates_of_not_acyclic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:27:09.387913+00:00
-- url     : https://prove2.me/theorems/b6ad42bb-a37e-4d4a-830d-f67aac41dc5e
-- title:
--   A graph that is not acyclic has a cycle in cyclic coordinates
-- statement:
--   Let $G$ be a simple graph on an arbitrary vertex set $V$. Cycle coordinates for $G$ consist of a natural number $n$ and an injective map $z:\mathbb{Z}/(n+3)\to V$ such that consecutive vertices are adjacent, $z_i\sim_G z_{i+1}$ for every $i\in\mathbb{Z}/(n+3)$. They list the vertices of a cycle of length $n+3\ge 3$ in cyclic order, with indices computed modulo the length.
--
--   **Theorem.** If $G$ is not acyclic, that is, some closed walk in $G$ is a cycle, then $G$ admits cycle coordinates:
--
--   $$\exists\,n\in\mathbb{N}\ \ \exists\,z:\mathbb{Z}/(n+3)\to V\ \text{injective}\ \ \forall i\in\mathbb{Z}/(n+3):\quad z_i\sim_G z_{i+1}.$$
--
--   The statement converts the walk-based notion of a cycle into indexed cyclic coordinates, the format in which cycles of dual graphs and of opposite graphs are handled throughout the Hamiltonicity proof, where arithmetic modulo the cycle length is used to move along the cycle.
--
--   **Formalization Note** The conclusion is `Nonempty (CycleCoordinates G)`, where `CycleCoordinates G` has fields `n`, `vertex : Fin (n + 3) ↪ V` and `adjacent`; addition on `Fin (n + 3)` is modulo $n+3$. Acyclicity is Mathlib's `SimpleGraph.IsAcyclic`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CycleReversal.lean#L13-L28

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

open OAI OAI.Barnette
open Fin.NatCast
variable {V : Type*} {G : SimpleGraph V}

theorem OAI.Barnette.cycleCoordinates_of_not_acyclic (hG : ¬G.IsAcyclic) :
    Nonempty (CycleCoordinates G) := by sorry
