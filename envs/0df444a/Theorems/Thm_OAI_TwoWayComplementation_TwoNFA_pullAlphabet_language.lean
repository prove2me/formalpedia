-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_pullAlphabet_language
-- name    : OAI.TwoWayComplementation.TwoNFA.pullAlphabet_language
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T03:58:00.8754+00:00
-- url     : https://prove2.me/theorems/ad860abb-6581-46ca-a148-75ca23bb5f95
-- title:
--   The letter pullback of a two-way automaton recognizes the preimage of its language
-- statement:
--   Let $\Sigma$ and $\Gamma$ be alphabets and $Q$ an arbitrary set of states. A two-way nondeterministic automaton (2NFA) $A$ over $\Gamma$ with state set $Q$ has an initial state $q_0$, an accepting set $F\subseteq Q$, and for every state $q$ and tape symbol $x\in\{\triangleright,\triangleleft\}\sqcup\Gamma$ a set $\delta_A(q,x)\subseteq Q\times\{0,1,2\}$ of next-state/move pairs (codes $0,1,2$ for left, stay, right). On an input $u=c_1\cdots c_n$ the tape reads $\triangleright c_1\cdots c_n\triangleleft$ at positions $0,\dots,n+1$; a step $(q,i)\to(r,j)$ uses a pair $(r,\mu)\in\delta_A(q,x_i)$, where $x_i$ is the symbol at position $i$, and requires $j=i+\mu-1\in\{0,\dots,n+1\}$. The language $L(A)$ is the set of words $u$ for which some finite, possibly empty, sequence of steps leads from $(q_0,0)$ to a configuration whose state lies in $F$.
--
--   For a map $f:\Sigma\to\Gamma$, the pullback $f^*A$ is the 2NFA over $\Sigma$ with the same states, initial state and accepting set, which treats the endmarkers as $A$ does and reads a letter $a\in\Sigma$ as $f(a)$: $\delta_{f^*A}(q,a)=\delta_A(q,f(a))$.
--
--   **Theorem.** For every word $w=a_1a_2\cdots a_n$ over $\Sigma$,
--   $$w\in L(f^*A)\iff f(a_1)f(a_2)\cdots f(a_n)\in L(A).$$
--   Equivalently, $L(f^*A)=\hat f^{-1}(L(A))$, where $\hat f:\Sigma^*\to\Gamma^*$ applies $f$ letter by letter.
--
--   Since $f^*A$ has the same state set as $A$, the theorem transfers automata between alphabets without changing the number of states. When $f$ is a bijection between two encodings of the same alphabet, the languages recognized under the two encodings correspond exactly, so upper and lower bounds on the number of states needed for a language, or for its complement, carry over from one encoding to the other.
--
--   **Formalization Note** The statement is `w ∈ (A.pullAlphabet f).language ↔ w.map f ∈ A.language` for `A : TwoNFA Gamma Q`, `f : Sigma → Gamma` and `w : List Sigma`; no finiteness of $Q$ is assumed, and acceptance uses the reflexive–transitive closure of the step relation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean#L60-L82

import Mathlib
import Definitions.Def_TwoWayDeterminization
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

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.TwoNFA.pullAlphabet_language {Sigma Gamma Q : Type*} (A : TwoNFA Gamma Q)
    (f : Sigma → Gamma) (w : List Sigma) :
    w ∈ (A.pullAlphabet f).language ↔ w.map f ∈ A.language := by sorry
