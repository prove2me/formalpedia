-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_chainStep_exitEquiv
-- name    : OAI.TwoWayComplementation.chainStep_exitEquiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:08:55.245876+00:00
-- url     : https://prove2.me/theorems/26deb4ac-0d7d-4e40-acc5-b7ab46a184c6
-- title:
--   Tape steps of a cell chain are its internal edges together with right exits to terminal vertices
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
--   Add to the vertices of $\mathcal{C}$ one terminal vertex $t_r$ for every label $r\in[m]$, and let $\mathcal{G}$ be the directed graph on the vertices of $\mathcal{C}$ and the terminal vertices whose edges are the internal edges $E$ of $\mathcal{C}$, the edges $v\to t_r$ for all $(v,r)\in O_R$, and no edges leaving a terminal vertex. Let $\Phi$ be the bijection onto $[m]\times\{0,\dots,n+1\}$ given by $\Phi(q,i)=(q,i)$ on vertices of $\mathcal{C}$ and $\Phi(t_r)=(r,n+1)$. Then for all vertices $x,y$ of $\mathcal{G}$,
--   $$
--   \Phi(x)\to_{\mathrm{tape}}\Phi(y)\iff x\to y\ \text{ in }\mathcal{G}.
--   $$
--
--   Thus the tape-step graph, including its terminal position, is isomorphic to the chain network with its right exits turned into edges to terminal vertices. This is the bridge between runs of a two-way machine from the left end of the tape to the terminal position and the forward component of the summary diagram of the chain.
--
--   **Formalization Note** The vertex type is `ChainNode m n`, defined recursively by `ChainNode m 0 = Fin m` and `ChainNode m (n + 1) = Fin m ⊕ ChainNode m n`, with coordinates `label` and `position`; the identification with pairs $(q,i)$ rests on `coordinates_injective`, `coordinates_surjective` and `position_le`. The network is `chainNetwork moves w last`, where the family $T$ is `moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)` with the moves $L,S,R$ encoded as `0, 1, 2 : Fin 3`, the final symbol $z$ is `last`, and the symbol of the cell of a vertex `c` is `chainSymbol w last c`, i.e. $\sigma_i$ for its position $i$. The tape-step relation is `chainStep moves w last` on `Fin m × Fin (w.length + 2)`; its definition asks for a chain vertex whose position is $i$ (such a vertex exists exactly when $i\le n$) and uses the symbol of that vertex, which is $\sigma_i$. Displacement equations are stated in the integers. The bijection $\Phi$ is `ChainNode.exitEquiv m n` on `ChainNode m n ⊕ Fin m`, and $\mathcal{G}$ is `blockRelation (chainNetwork moves w last).edge (chainNetwork moves w last).rightOut ∅ ∅`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean#L103-L146

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

theorem OAI.TwoWayComplementation.chainStep_exitEquiv {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (x y : ChainNode m w.length ⊕ Fin m) :
    (ChainNode.exitEquiv m w.length x, ChainNode.exitEquiv m w.length y) ∈
        chainStep moves w last ↔
      (x, y) ∈ blockRelation (chainNetwork moves w last).edge
        (chainNetwork moves w last).rightOut ∅ ∅ := by sorry
