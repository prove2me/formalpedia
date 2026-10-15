-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_PathNFA_good_step
-- name    : OAI.OneWayLiveness.PathNFA.good_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:31:41.667982+00:00
-- url     : https://prove2.me/theorems/b9282867-7b72-4ddc-ad47-19e1c6224e90
-- title:
--   Every step of the path automaton preserves its prefix-path invariant
-- statement:
--   A word $w=a_1\cdots a_n$ is read by a two-way automaton on the tape $\vdash a_1\cdots a_n\dashv$ with cells $0,1,\dots,n+1$: cell $0$ holds the left endmarker $\vdash$, cell $k$ ($1\le k\le n$) holds $a_k$, and cell $n+1$ holds the right endmarker $\dashv$. A configuration is a pair $(k,q)$ of a head position $k\in\{0,\dots,n+1\}$ and a state $q$; a step from $(k,q)$ applies a transition for the symbol in cell $k$, which specifies a new state and a move of the head by $-1$, $0$ or $+1$.
--
--   Let $H$ be an arbitrary set and consider words $w=R_1\cdots R_n$ over the alphabet $\mathcal R_H$ of all binary relations on $H$. Products of relations are compositions in diagrammatic order ($(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$), the empty product being the identity relation $\Delta_H$. The path automaton $N_H$ is the nondeterministic two-way automaton with states $\mathsf{start}$, a path state $\langle p\rangle$ for each $p\in H$, an accepting state $\mathsf{acc}$ and an unused state $\mathsf{rej}$, initial state $\mathsf{start}$ and accepting set $\{\mathsf{acc}\}$, whose only transitions are:
--   1. in $\mathsf{start}$ reading $\vdash$: move right and enter any $\langle p\rangle$, $p\in H$;
--   2. in $\langle p\rangle$ reading a letter $R$: move right and enter any $\langle q\rangle$ with $(p,q)\in R$;
--   3. in $\langle p\rangle$ reading $\dashv$: stay and enter $\mathsf{acc}$.
--
--   For a word $w=R_1\cdots R_n$ define a property $G_w$ of configurations by
--
--   $$G_w(k,\mathsf{start})\iff k=0,\qquad G_w(k,\langle p\rangle)\iff k\ge1\ \text{and}\ (a,p)\in R_1\cdots R_{k-1}\ \text{for some } a\in H,$$
--
--   $G_w(k,\mathsf{acc})$ holds iff $R_1R_2\cdots R_n\neq\varnothing$, and $G_w(k,\mathsf{rej})$ never holds; for $k=1$ the product $R_1\cdots R_{k-1}$ is empty, i.e. the identity. Then for all configurations $c,c'$ of $N_H$ on $w$: if $G_w(c)$ holds and $c'$ is reachable from $c$ by one step of $N_H$, then $G_w(c')$ holds.
--
--   The property $G_w$ holds at the start configuration $(0,\mathsf{start})$, so by this lemma it holds along every run; at the accepting state it says that $w$ is live. This is the soundness half of the correctness proof of the path automaton.
--
--   **Formalization Note** The states are `Option (H ⊕ Bool)`: `none` is $\mathsf{start}$, `some (inl p)` is $\langle p\rangle$, `some (inr false)` is $\mathsf{acc}$ and `some (inr true)` is $\mathsf{rej}$. The automaton is `PathNFA.machine`, the invariant is `PathNFA.Good`, the prefix product is `(w.take (k-1)).prod` and the step relation is `NMachineOn.Step`. No finiteness of $H$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/PathNFA.lean#L136-L190

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.PathNFA
variable {H : Type}

theorem OAI.OneWayLiveness.PathNFA.good_step (w : List (BRel H)) (c c' : NMachineOn.Config (Q := State H) w)
    (hg : Good w c) (hs : machine.Step w c c') : Good w c' := by sorry
