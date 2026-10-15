-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_augmented_run_cases
-- name    : OAI.TwoWayComplementation.TwoNFA.augmented_run_cases
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:56:06.868363+00:00
-- url     : https://prove2.me/theorems/a589eb47-f281-4e33-8dda-ec23cdcfa8d8
-- title:
--   Augmented runs of a two-way automaton stay in the original configuration graph until acceptance
-- statement:
--   Let $\Sigma$ be an alphabet and let $A=(Q,q_0,F,\delta)$ be a two-way nondeterministic automaton over $\Sigma$: $Q$ is an arbitrary set of states, $q_0\in Q$ is the initial state, $F\subseteq Q$ is the set of accepting states, and $\delta$ assigns to every state $q$ and every tape symbol $b\in\{\vdash,\dashv\}\sqcup\Sigma$ a set $\delta(q,b)\subseteq Q\times\{L,S,R\}$ of pairs (next state, head move). A word $w=a_1\cdots a_n\in\Sigma^*$ is written on the tape positions $0,1,\dots,n+1$ as $\vdash a_1\cdots a_n\dashv$, and $b_i$ denotes the symbol at position $i$. A configuration is a pair $(q,i)$ with $q\in Q$ and $0\le i\le n+1$, and $(q,i)\to(q',j)$ is a step if $(q',\mu)\in\delta(q,b_i)$ and $j=i+\Delta(\mu)$, where $\Delta(L)=-1$, $\Delta(S)=0$, $\Delta(R)=1$; a move that would leave the tape is not a step. The language $\mathcal{L}(A)$ is the set of words $w$ for which some configuration with an accepting state is reachable from $(q_0,0)$ by finitely many steps, possibly none; $\to^{*}$ denotes this reachability.
--
--   Fix a word $w=a_1\cdots a_n$. The augmented configuration graph of $A$ on $w$ uses a fresh state $f\notin Q$ and one extra position $n+2$ to the right of $\dashv$. Its vertices are the pairs $(s,i)$ with $s\in Q\sqcup\{f\}$ and $0\le i\le n+2$, and its edges $c\rightsquigarrow d$ are of three kinds:
--
--   $$
--   \begin{aligned}
--   &(q,i)\rightsquigarrow(q',j) && \text{whenever } (q,i)\to(q',j) \text{ is a step of } A \text{ on } w,\\
--   &(q,i)\rightsquigarrow(f,i) && \text{whenever } q\in F \text{ and } 0\le i\le n+1,\\
--   &(f,i)\rightsquigarrow(f,i+1) && \text{for } 0\le i\le n+1 .
--   \end{aligned}
--   $$
--
--   Configurations of $A$ are embedded by $\iota(q,i)=(q,i)$, and $\rightsquigarrow^{*}$ denotes reachability by zero or more edges.
--
--   If a vertex $c$ of the augmented graph is reachable from the embedded initial configuration, $\iota(q_0,0)\rightsquigarrow^{*}c$, then
--   $$
--   w\in\mathcal{L}(A)\qquad\text{or}\qquad c=\iota(x)\ \text{ for some configuration } x \text{ of } A \text{ with } (q_0,0)\to^{*}x .
--   $$
--
--   In words, an augmented run that does not witness acceptance stays inside the embedded copy of the configuration graph of $A$; the fresh state can only be entered from an accepting configuration. This is the soundness half of the characterization of acceptance as reachability of the single vertex $(f,n+2)$.
--
--   **Formalization Note** `TwoNFA Sigma Q` has fields `initial`, `accepting` and `transition`; tape symbols are `Fin 2 ⊕ Sigma` with `Sum.inl 0` and `Sum.inl 1` the endmarkers $\vdash$ and $\dashv$ (read by `tapeSymbol w`), the moves $L,S,R$ are `0, 1, 2 : Fin 3` with displacement `move.val - 1` computed in the integers, configurations are `Q × Fin (w.length + 2)`, the step relation is `A.step w`, and reachability is `relStar`, the reflexive–transitive closure. The fresh state is `none : Option Q`, the states of $Q$ appear as `some q`, and augmented positions are `Fin (w.length + 3)`; $\iota$ is `augmentConfig`, which applies `some` to the state and `Fin.castSucc` to the position, and the edge relation $\rightsquigarrow$ is `A.augmentedStep w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean#L67-L83

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.TwoNFA
open scoped SetRel

theorem OAI.TwoWayComplementation.TwoNFA.augmented_run_cases {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    {c : Option Q × Fin (w.length + 3)}
    (hrun : (augmentConfig (A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.augmentedStep w)) :
    w ∈ A.language ∨ ∃ x : Q × Fin (w.length + 2),
      c = augmentConfig x ∧ ((A.initial, ⟨0, by omega⟩), x) ∈ relStar (A.step w) := by sorry
