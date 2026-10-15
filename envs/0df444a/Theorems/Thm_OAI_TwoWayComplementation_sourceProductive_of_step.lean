-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_sourceProductive_of_step
-- name    : OAI.TwoWayComplementation.sourceProductive_of_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:58:05.716462+00:00
-- url     : https://prove2.me/theorems/f4e2623b-a5b8-4427-a88d-6803e72ac11b
-- title:
--   Productive configurations of the relation-product automaton are closed under predecessors
-- statement:
--   Let $H$ be a set and let $\mathrm{Rel}(H)$ be the set of binary relations on $H$, used as an input alphabet. For a word $w=X_1X_2\cdots X_n$ over $\mathrm{Rel}(H)$ let $\pi(w)=X_1X_2\cdots X_n$ be the composite relation in path order, so that $(x,y)\in\pi(w)$ iff there are $x=x_0,x_1,\dots,x_n=y$ with $(x_{k-1},x_k)\in X_k$ for all $k$; the empty product is the identity $\mathrm{id}_H$.
--
--   Two-way nondeterministic automata are as usual: the input is written as $\vdash X_1\cdots X_n\dashv$ on positions $0,\dots,n+1$, a configuration is a pair (state, position), and $(s,i)\to(s',j)$ is a step if $(s',\mu)\in\delta(s,b_i)$ for the symbol $b_i$ at position $i$ and a move $\mu\in\{L,S,R\}$ with $j=i+\Delta(\mu)$, where $\Delta(L)=-1$, $\Delta(S)=0$, $\Delta(R)=1$. The relation-product automaton $A_H$ has the states $q_{\mathrm{st}}$ (initial), $q_{\mathrm{acc}}$ (the only accepting state) and $\langle h\rangle$ for $h\in H$, and the transitions
--   $$
--   \delta(q_{\mathrm{st}},\vdash)=\{(\langle h\rangle,R):h\in H\},\qquad \delta(\langle p\rangle,X)=\{(\langle q\rangle,R):(p,q)\in X\}\ \ (X\in\mathrm{Rel}(H)),\qquad \delta(\langle p\rangle,\dashv)=\{(q_{\mathrm{acc}},S)\},
--   $$
--   all other transition sets being empty. For a word $w=X_1\cdots X_n$, the set $P_w$ of productive configurations consists of
--   1. $(q_{\mathrm{st}},0)$, provided $\pi(w)\neq\varnothing$ (no other configuration with state $q_{\mathrm{st}}$ belongs to $P_w$);
--   2. $(q_{\mathrm{acc}},i)$ for every position $0\le i\le n+1$;
--   3. $(\langle p\rangle,i)$ for $1\le i\le n+1$ such that $(p,q)\in\pi(X_iX_{i+1}\cdots X_n)$ for some $q\in H$; for $i=n+1$ the suffix is empty, so $(\langle p\rangle,n+1)\in P_w$ for every $p$.
--
--   Then $P_w$ is closed under taking predecessors: for all configurations $c,d$ of $A_H$ on $w$,
--   $$
--   c\to d\ \text{ and }\ d\in P_w\ \Longrightarrow\ c\in P_w .
--   $$
--
--   Since every configuration with state $q_{\mathrm{acc}}$ is productive, it follows along any accepting run that the initial configuration $(q_{\mathrm{st}},0)$ is productive, i.e. $\pi(w)\neq\varnothing$; this is the soundness of $A_H$. Together with the converse, shown separately, $A_H$ recognizes exactly the words of relations on $H$ with nonempty product, using $|H|+2$ states; for $H=\{0,\dots,n-3\}$ this is the $n$-state automaton whose complement is shown to be expensive.
--
--   **Formalization Note** The state set is `Option (Option H)`, with `none` for $q_{\mathrm{st}}$, `some none` for $q_{\mathrm{acc}}$ and `some (some h)` for $\langle h\rangle$; the automaton is `sourceAutomaton H` and $P_w$ is `sourceProductive w`. The product $\pi$ is `relationProduct`, a right fold of `SetRel.comp` starting from `SetRel.id`, the suffix $X_i\cdots X_n$ is `w.drop (i - 1)`, and $\pi(w)\neq\varnothing$ is `(relationProduct w).Nonempty`. Endmarkers and moves are encoded as in `TwoNFA` (`Sum.inl 0`, `Sum.inl 1`; `0, 1, 2 : Fin 3` for $L,S,R$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Source.lean#L46-L94

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

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.sourceProductive_of_step {H : Type*} (w : List (SetRel H H))
    {c d : Option (Option H) × Fin (w.length + 2)}
    (hstep : (c, d) ∈ (sourceAutomaton H).step w) (hd : d ∈ sourceProductive w) :
    c ∈ sourceProductive w := by sorry
