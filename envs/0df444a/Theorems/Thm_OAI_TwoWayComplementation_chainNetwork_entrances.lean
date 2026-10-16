-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_chainNetwork_entrances
-- name    : OAI.TwoWayComplementation.chainNetwork_entrances
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:03:09.472911+00:00
-- url     : https://prove2.me/theorems/7ec6ef02-00e2-4aa7-8bee-4a8807b828df
-- title:
--   Entrances of a chain of cell networks: label $q$ enters at the first cell on the left and at the last cell on the right
-- statement:
--   Let $m\in\mathbb{N}$, write $[m]=\{0,1,\dots,m-1\}$ for the set of state labels, and let $\Sigma$ be a set of symbols. Fix a family of relations $T_a(\mu)\subseteq[m]\times[m]$, one for every symbol $a\in\Sigma$ and every move $\mu\in\{L,S,R\}$; the moves have displacements $\Delta(L)=-1$, $\Delta(S)=0$, $\Delta(R)=1$. A network with $m$ boundary labels on a vertex set $V$ consists of internal edges $E\subseteq V\times V$, left and right entrances $I_L,I_R\subseteq[m]\times V$, and left and right exits $O_L,O_R\subseteq V\times[m]$. The cell network of a symbol $a$ has vertex set $[m]$, internal edges $T_a(S)$, the identity relation as left and as right entrances, left exits $T_a(L)$ and right exits $T_a(R)$. Two networks are joined side by side on the disjoint union of their vertex sets: the left entrances and exits are those of the first network, the right entrances and exits are those of the second, and besides the internal edges of both there are crossing edges $v\to v'$ whenever $v$ exits the first network on the right with a label at which $v'$ enters the second on the left, and $v'\to v$ whenever $v'$ exits the second network on the left with a label at which $v$ enters the first on the right.
--
--   For a word $w=w_0w_1\cdots w_{n-1}\in\Sigma^*$ and a final symbol $z\in\Sigma$, the chain network $\mathcal{C}=\mathcal{C}_T(w,z)$ is the cell network of $z$ if $n=0$, and the join of the cell network of $w_0$ with $\mathcal{C}_T(w_1\cdots w_{n-1},z)$ otherwise. It has $n+1$ cells at positions $0,1,\dots,n$, carrying the symbols $\sigma_i=w_i$ for $i<n$ and $\sigma_n=z$, and every vertex of $\mathcal{C}$ is identified with the pair $(q,i)$ of its state label $q\in[m]$ and its cell position $i\in\{0,\dots,n\}$; every such pair occurs exactly once. Write $E$, $I_L$, $I_R$, $O_L$, $O_R$ for the parts of $\mathcal{C}$.
--
--   Then for every label $q\in[m]$ and every vertex $(q',i)$ of $\mathcal{C}$ the following hold.
--   1. Left entrances are at the first cell:
--   $$
--   (q,(q',i))\in I_L\iff i=0\ \text{and}\ q'=q .
--   $$
--   2. Right entrances are at the last cell:
--   $$
--   (q,(q',i))\in I_R\iff i=n\ \text{and}\ q'=q .
--   $$
--
--   So the label $q$ enters the chain from the left at the vertex with label $q$ in the first cell, and from the right at the vertex with label $q$ in the last cell, without any transition being applied. Together with the descriptions of exits and internal edges, this identifies the chain network with the configuration graph of a two-way machine on a tape of $n+1$ cells.
--
--   **Formalization Note** The vertex type is `ChainNode m n`, defined recursively by `ChainNode m 0 = Fin m` and `ChainNode m (n + 1) = Fin m ⊕ ChainNode m n`, with coordinates `label` and `position`; the identification with pairs $(q,i)$ rests on `coordinates_injective`, `coordinates_surjective` and `position_le`. The network is `chainNetwork moves w last`, where the family $T$ is `moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)` with the moves $L,S,R$ encoded as `0, 1, 2 : Fin 3`, the final symbol $z$ is `last`, and the symbol of the cell of a vertex `c` is `chainSymbol w last c`, i.e. $\sigma_i$ for its position $i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean#L108-L132

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

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.chainNetwork_entrances {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q : Fin m) (c : ChainNode m w.length) :
    ((q, c) ∈ (chainNetwork moves w last).leftIn ↔ c.position = 0 ∧ q = c.label) ∧
    ((q, c) ∈ (chainNetwork moves w last).rightIn ↔ c.position = w.length ∧ q = c.label) := by sorry
