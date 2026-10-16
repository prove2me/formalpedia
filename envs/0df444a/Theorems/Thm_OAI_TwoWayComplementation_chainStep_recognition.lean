-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_chainStep_recognition
-- name    : OAI.TwoWayComplementation.chainStep_recognition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:09:50.586059+00:00
-- url     : https://prove2.me/theorems/c587095a-5d57-4f0f-b129-2b990cdcb024
-- title:
--   Forward connections of a cell chain are exactly tape runs from the left end to the terminal position
-- statement:
--   Let $m\in\mathbb{N}$, write $[m]=\{0,1,\dots,m-1\}$ for the set of state labels, and let $\Sigma$ be a set of symbols. Fix a family of relations $T_a(\mu)\subseteq[m]\times[m]$, one for every symbol $a\in\Sigma$ and every move $\mu\in\{L,S,R\}$; the moves have displacements $\Delta(L)=-1$, $\Delta(S)=0$, $\Delta(R)=1$. A network with $m$ boundary labels on a vertex set $V$ consists of internal edges $E\subseteq V\times V$, left and right entrances $I_L,I_R\subseteq[m]\times V$, and left and right exits $O_L,O_R\subseteq V\times[m]$. The cell network of a symbol $a$ has vertex set $[m]$, internal edges $T_a(S)$, the identity relation as left and as right entrances, left exits $T_a(L)$ and right exits $T_a(R)$. Two networks are joined side by side on the disjoint union of their vertex sets: the left entrances and exits are those of the first network, the right entrances and exits are those of the second, and besides the internal edges of both there are crossing edges $v\to v'$ whenever $v$ exits the first network on the right with a label at which $v'$ enters the second on the left, and $v'\to v$ whenever $v'$ exits the second network on the left with a label at which $v$ enters the first on the right.
--
--   For a word $w=w_0w_1\cdots w_{n-1}\in\Sigma^*$ and a final symbol $z\in\Sigma$, the chain network $\mathcal{C}=\mathcal{C}_T(w,z)$ is the cell network of $z$ if $n=0$, and the join of the cell network of $w_0$ with $\mathcal{C}_T(w_1\cdots w_{n-1},z)$ otherwise. It has $n+1$ cells at positions $0,1,\dots,n$, carrying the symbols $\sigma_i=w_i$ for $i<n$ and $\sigma_n=z$, and every vertex of $\mathcal{C}$ is identified with the pair $(q,i)$ of its state label $q\in[m]$ and its cell position $i\in\{0,\dots,n\}$; every such pair occurs exactly once. Write $E$, $I_L$, $I_R$, $O_L$, $O_R$ for the parts of $\mathcal{C}$.
--
--   The tape-step relation of the chain is the relation $\to_{\mathrm{tape}}$ on $[m]\times\{0,1,\dots,n+1\}$ defined by
--   $$
--   (q,i)\to_{\mathrm{tape}}(r,j)\iff i\le n\ \text{ and there is }\mu\in\{L,S,R\}\text{ with }(q,r)\in T_{\sigma_i}(\mu)\ \text{and}\ j=i+\Delta(\mu);
--   $$
--   the position $n+1$ is a terminal position beyond the last cell, from which there are no steps.
--
--   The forward component of the summary diagram of $\mathcal{C}$ is the relation $I_L\,E^{*}\,O_R$ on $[m]$, where $E^{*}$ is the reflexive–transitive closure of $E$ and relations are composed in path order: $(q,r)\in I_LE^{*}O_R$ iff some path of internal edges leads from a vertex at which $q$ enters on the left to a vertex that exits on the right with label $r$. Then for all labels $q,r\in[m]$,
--   $$
--   (q,0)\to_{\mathrm{tape}}^{*}(r,n+1)\iff (q,r)\in I_L\,E^{*}\,O_R ,
--   $$
--   where $\to_{\mathrm{tape}}^{*}$ denotes reachability by zero or more tape steps.
--
--   Since the summary of a chain of cells is the product of the cell diagrams of $\sigma_0,\dots,\sigma_n$, this identifies the forward component of such a product with runs of a two-way machine from the left end of the tape to the terminal position. Applied to an automaton augmented by a fresh exit state, with cells $\vdash,a_1,\dots,a_n$ and final cell $\dashv$, it expresses acceptance of $a_1\cdots a_n$ as one forward connection in a product of diagrams.
--
--   **Formalization Note** The vertex type is `ChainNode m n`, defined recursively by `ChainNode m 0 = Fin m` and `ChainNode m (n + 1) = Fin m ⊕ ChainNode m n`, with coordinates `label` and `position`; the identification with pairs $(q,i)$ rests on `coordinates_injective`, `coordinates_surjective` and `position_le`. The network is `chainNetwork moves w last`, where the family $T$ is `moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)` with the moves $L,S,R$ encoded as `0, 1, 2 : Fin 3`, the final symbol $z$ is `last`, and the symbol of the cell of a vertex `c` is `chainSymbol w last c`, i.e. $\sigma_i$ for its position $i$. The tape-step relation is `chainStep moves w last` on `Fin m × Fin (w.length + 2)`; its definition asks for a chain vertex whose position is $i$ (such a vertex exists exactly when $i\le n$) and uses the symbol of that vertex, which is $\sigma_i$. Displacement equations are stated in the integers. The right-hand side is `(chainNetwork moves w last).summary.forward`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean#L148-L169

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.chainStep_recognition {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q r : Fin m) :
    ((q, ⟨0, by omega⟩), (r, ⟨w.length + 1, by omega⟩)) ∈ relStar (chainStep moves w last) ↔
      (q, r) ∈ (chainNetwork moves w last).summary.forward := by sorry
