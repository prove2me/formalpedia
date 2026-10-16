-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_complementation_lower_bound
-- name    : OAI.TwoWayComplementation.complementation_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:11:45.782164+00:00
-- url     : https://prove2.me/theorems/53525802-d51a-4919-9505-c556d451d8af
-- title:
--   An $n$-state two-way NFA whose complement requires at least $2^{\lfloor (n-4)/127\rfloor-1}-1$ states
-- statement:
--   A two-way nondeterministic finite automaton (2NFA) $A$ over an alphabet $\Sigma$ with state set $Q$ consists of an initial state $q_0\in Q$, a set $F\subseteq Q$ of accepting states and a transition map assigning to each state $q$ and each tape symbol $x\in\{\vdash,\dashv\}\sqcup\Sigma$ a set $\delta(q,x)\subseteq Q\times\{-1,0,+1\}$ of allowed pairs (next state, head move). A word $w=a_1\cdots a_n\in\Sigma^{*}$ is written on the tape $\vdash a_1\cdots a_n\dashv$ with cells $0,1,\dots,n+1$: the left endmarker $\vdash$ in cell $0$, the letter $a_k$ in cell $k$ and the right endmarker $\dashv$ in cell $n+1$. A configuration is a pair $(q,k)$ of a state $q$ and a head position $k\in\{0,\dots,n+1\}$, and $(q,k)\to(q',k')$ is a step if $(q',k'-k)\in\delta(q,x_k)$, where $x_k$ is the symbol in cell $k$; in particular the head never leaves the tape. The automaton accepts $w$ if some configuration whose state lies in $F$ is reachable from $(q_0,0)$ by a run of zero or more steps (no halting condition is imposed), and $L(A)\subseteq\Sigma^{*}$ denotes the set of accepted words.
--
--   For $h\in\mathbb{N}$ let $[h]=\{0,\dots,h-1\}$ and let $\Sigma_h$ be the alphabet whose letters are all binary relations on $[h]$, i.e. all subsets of $[h]\times[h]$; it is a finite alphabet with $2^{h^2}$ letters.
--
--   **Theorem.** For every integer $n\ge4$ there is a 2NFA $A$ over $\Sigma_{n-2}$ with state set $[n]$ (so $A$ has $n$ states) such that for every $s\in\mathbb{N}$ and every 2NFA $B$ over $\Sigma_{n-2}$ with state set $[s]$,
--
--   $$
--   L(B)=\Sigma_{n-2}^{*}\setminus L(A)\quad\Longrightarrow\quad 2^{\lfloor (n-4)/127\rfloor}\le 2\,(s+1).
--   $$
--
--   Equivalently, every 2NFA over $\Sigma_{n-2}$ accepting exactly the words rejected by $A$ has at least $2^{\lfloor (n-4)/127\rfloor-1}-1$ states. So, over alphabets that grow with $n$, complementing an $n$-state two-way nondeterministic automaton can require a number of states exponential in $n/127$; in particular, no polynomial in $n$ bounds the number of states needed to complement $n$-state 2NFAs. The version for arbitrary finite state sets, $|Q|\ge\frac12\cdot 2^{\lfloor (n-4)/127\rfloor}-1$, follows by renaming states.
--
--   **Formalization Note** The alphabet is `SetRel (Fin (n - 2)) (Fin (n - 2))`, the automata are `A : TwoNFA _ (Fin n)` and `B : TwoNFA _ (Fin s)`, and the hypothesis $L(B)=\Sigma_{n-2}^{*}\setminus L(A)$ is the set equation `B.language = A.languageᶜ`. The exponent `(n - 4) / 127` is natural-number division, i.e. the floor; since $n\ge4$ the subtraction does not truncate. The inequality is stated in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean#L10-L28

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

theorem OAI.TwoWayComplementation.complementation_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ s : ℕ, ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin s),
        B.language = A.languageᶜ → 2 ^ ((n - 4) / 127) ≤ 2 * (s + 1) := by sorry
