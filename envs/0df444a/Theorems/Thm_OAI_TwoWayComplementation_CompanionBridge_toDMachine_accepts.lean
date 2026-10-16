-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_CompanionBridge_toDMachine_accepts
-- name    : OAI.TwoWayComplementation.CompanionBridge.toDMachine_accepts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:00:20.888956+00:00
-- url     : https://prove2.me/theorems/c0089445-6bc8-444e-ad41-cf861e92a27d
-- title:
--   The companion deterministic machine of a deterministic 2NFA accepts exactly the same words
-- statement:
--   Let $\Sigma$ be an alphabet, $s\in\mathbb N$ and $[s]=\{0,\dots,s-1\}$.
--
--   *Two-way automata.* A 2NFA $A$ over $\Sigma$ with state set $[s]$ has an initial state $q_0$, an accepting set $F\subseteq[s]$, and for every state $q$ and tape symbol $x\in\{\triangleright,\triangleleft\}\sqcup\Sigma$ a set $\delta(q,x)\subseteq[s]\times\{0,1,2\}$ of next-state/move pairs (codes $0,1,2$ for left, stay, right). On $w=a_1\cdots a_n$ the tape $\triangleright a_1\cdots a_n\triangleleft$ has positions $0,\dots,n+1$; a step $(q,i)\to(r,j)$ requires $(r,\mu)\in\delta(q,x_i)$ for the symbol $x_i$ at position $i$ and $j=i+\mu-1\in\{0,\dots,n+1\}$. $L(A)$ is the set of words $w$ for which a finite, possibly empty, run leads from $(q_0,0)$ to a configuration with state in $F$. $A$ is deterministic if every $\delta(q,x)$ has at most one element.
--
--   *Companion deterministic machines.* Such a machine $D$ with $s$ states has an initial state, an accepting set and a partial transition function giving, for each state $q$ and tape symbol $x$, either nothing or one pair $(r,M)$ with $M\in\{\mathrm L,\mathrm S,\mathrm R\}$, never $\mathrm L$ on $\triangleright$ and never $\mathrm R$ on $\triangleleft$. A step goes from (position $i$, state $q$) to (position $j$, state $r$) when $\delta_D(q,x_i)=(r,M)$ and $j=i-1$, $i$ or $i+1$ for $M=\mathrm L,\mathrm S,\mathrm R$ respectively. Under the reflexive acceptance convention, $D$ accepts $w$ if a run of length at least $0$ leads from (position $0$, initial state) to a configuration whose state is accepting.
--
--   *The conversion.* For deterministic $A$, the machine $D_A$ has the states, initial state and accepting set of $A$, and $\delta_{D_A}(q,x)$ is the unique pair $(r,M)$ with $(r,\mathrm{code}(M))\in\delta(q,x)$ such that $M$ is not $\mathrm L$ on $\triangleright$ and not $\mathrm R$ on $\triangleleft$, and is undefined if there is no such pair; here $\mathrm{code}(\mathrm L)=0$, $\mathrm{code}(\mathrm S)=1$, $\mathrm{code}(\mathrm R)=2$.
--
--   **Theorem.** For every deterministic 2NFA $A$ with state set $[s]$ and every word $w$ over $\Sigma$,
--   $$D_A\ \text{accepts}\ w\ \text{(runs of length}\ \ge 0\text{ allowed)}\iff w\in L(A).$$
--
--   Thus every deterministic 2NFA with $s$ states yields a companion deterministic machine with the same $s$ states recognizing the same language, so any lower bound on the number of states of companion deterministic machines for a language is also a lower bound for deterministic 2NFAs. No halting or totality assumption is involved: acceptance on both sides is reachability of an accepting state.
--
--   **Formalization Note** The statement is `(toDMachine A hA).Accepts false w ↔ w ∈ A.language` for `A : TwoNFA Alpha (Fin s)` and `hA : A.Deterministic`. The flag `false` selects the reflexive–transitive closure of the step relation (`true` would demand at least one step). Configurations of `DMachine` are pairs (position, state), while those of `TwoNFA` are pairs (state, position).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/TransitionBridge.lean#L123-L137

import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.CompanionBridge
open OneWayLiveness

theorem OAI.TwoWayComplementation.CompanionBridge.toDMachine_accepts {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (w : List Alpha) :
    (toDMachine A hA).Accepts false w ↔ w ∈ A.language := by sorry
