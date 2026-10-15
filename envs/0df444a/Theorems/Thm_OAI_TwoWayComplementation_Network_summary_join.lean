-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Network_summary_join
-- name    : OAI.TwoWayComplementation.Network.summary_join
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:01:44.441186+00:00
-- url     : https://prove2.me/theorems/8577dcef-e3df-48b5-b7be-a9d4f4eb02d2
-- title:
--   The path summary of two joined networks is the product of their boundary diagrams
-- statement:
--   For $m\in\mathbb{N}$ let $[m]=\{0,1,\dots,m-1\}$. Binary relations are composed in path order, $(x,z)\in PQ$ iff $(x,y)\in P$ and $(y,z)\in Q$ for some $y$, and $P^{*}$ denotes the reflexive–transitive closure of a relation $P$ on a set. A boundary diagram on $m$ labels is a quadruple $a=(F_a,B_a,L_a,R_a)$ of relations on $[m]$, read as the connections of a two-sided gadget: forward (enter on the left, leave on the right), backward (enter on the right, leave on the left), left return (enter and leave on the left) and right return (enter and leave on the right). The diagrams form a monoid $\mathcal{D}_m$ under the path-order product
--   $$
--   \begin{aligned}
--   F_{ab}&=F_a(L_bR_a)^{*}F_b, & B_{ab}&=B_b(R_aL_b)^{*}B_a,\\
--   L_{ab}&=L_a\cup F_a(L_bR_a)^{*}L_bB_a, & R_{ab}&=R_b\cup B_bR_a(L_bR_a)^{*}F_b,
--   \end{aligned}
--   $$
--   with identity $\mathbf{1}=(\mathrm{id},\mathrm{id},\varnothing,\varnothing)$, and they are ordered componentwise: $a\sqsubseteq a'$ means $F_a\subseteq F_{a'}$, $B_a\subseteq B_{a'}$, $L_a\subseteq L_{a'}$ and $R_a\subseteq R_{a'}$.
--
--   A network $N$ with $m$ boundary labels on a vertex set $V$ consists of internal edges $E\subseteq V\times V$, left and right entrances $I_L,I_R\subseteq[m]\times V$, and left and right exits $O_L,O_R\subseteq V\times[m]$. Its summary is the diagram
--   $$
--   \widehat N=\bigl(I_LE^{*}O_R,\ I_RE^{*}O_L,\ I_LE^{*}O_L,\ I_RE^{*}O_R\bigr),
--   $$
--   which records which labels are connected by finite internal paths between the four pairs of sides. For a second network $M=(E',I'_L,I'_R,O'_L,O'_R)$ on a vertex set $W$, the join $N\bowtie M$ is the network on $V\sqcup W$ with left entrances $I_L$ and left exits $O_L$ (attached to $V$), right entrances $I'_R$ and right exits $O'_R$ (attached to $W$), and internal edges given by $E$ on $V$, by $E'$ on $W$, by $O_RI'_L$ from $V$ to $W$ and by $O'_LI_R$ from $W$ to $V$. Thus a vertex of $N$ that exits on the right with some label is wired to every vertex of $M$ that this label enters on the left, and vice versa.
--
--   Then for all networks $N$ and $M$ with $m$ boundary labels, on arbitrary vertex sets,
--   $$
--   \widehat{N\bowtie M}=\widehat N\,\widehat M .
--   $$
--
--   Gluing networks side by side is therefore reflected exactly by the product of their summary diagrams. By induction, the summary of a chain of cell networks is the product of the cell diagrams; this is how the computation of a two-way automaton on a word becomes a product of one diagram per tape symbol.
--
--   **Formalization Note** `Network m V` is a structure with fields `edge`, `leftIn`, `rightIn`, `leftOut`, `rightOut`; `summary` and `join` are as above, the edge relation of the join being `blockRelation` with the four blocks on `V ⊕ W`. The product is `Diagram.comp`, composition `○` of `SetRel` is in path order, and $P^{*}$ is `relStar`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Network.lean#L108-L183

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

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Network
open scoped SetRel

theorem OAI.TwoWayComplementation.Network.summary_join {m : ℕ} {V W : Type*} (N : Network m V) (M : Network m W) :
    (N.join M).summary = Diagram.comp N.summary M.summary := by sorry
