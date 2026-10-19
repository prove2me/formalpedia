-- Prove2me | Theorems.Thm_OAI_Barnette_Network_white_positive_of_boundary
-- name    : OAI.Barnette.Network.white_positive_of_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:24:35.645233+00:00
-- url     : https://prove2.me/theorems/72b9ab7f-a69e-49e9-a91e-d57e218051d4
-- title:
--   A vertex set with cut imbalance $|\delta(A)|=2|\delta_B(A)|+3$ contains a white vertex
-- statement:
--   Let $N$ be a network with vertex set $V$ and finite edge set $E$, each edge $e$ having a tail $t(e)$ and a head $h(e)$ in $V$. Let $B\subseteq V$ be a set of *black* vertices such that every edge has exactly one black endpoint ($t(e)\in B$ if and only if $h(e)\notin B$), and write $b(e)$ for the black endpoint of $e$. For a finite set $A\subseteq V$ let $\delta(A)$ be the set of edges with exactly one endpoint in $A$, and let $\delta_B(A)=\{e\in\delta(A): b(e)\in A\}$.
--
--   If $|\delta(A)|=2|\delta_B(A)|+3$, then $A$ contains a vertex that is not black:
--
--   $$
--   |\{v\in A: v\notin B\}|>0 .
--   $$
--
--   The hypothesis is exactly the cut imbalance satisfied by the disk bounded by a state cycle. The conclusion guarantees that such a disk carries a positive amount of white charge, which makes the integral of the white-charge flow around the cycle nonzero with a known sign.
--
--   **Formalization Note** The colouring is a predicate `black : V → Prop` with `∀ e, black (N.tail e) ↔ ¬black (N.head e)`; $\delta_B(A)$ is `N.blackCut black A`, built from `N.blackEndpoint black e` (the tail if it is black, otherwise the head). The vertex type need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Circulation.lean#L226-L248

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.white_positive_of_boundary (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (A : Finset V)
    (hcount : (N.cut A).card = 2 * (N.blackCut black A).card + 3) :
    0 < (A.filter fun v => ¬black v).card := by sorry
