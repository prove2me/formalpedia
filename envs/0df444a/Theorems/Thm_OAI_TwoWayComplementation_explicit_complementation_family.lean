-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_explicit_complementation_family
-- name    : OAI.TwoWayComplementation.explicit_complementation_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:05:23.354815+00:00
-- url     : https://prove2.me/theorems/c92e62f5-3900-4e2c-824d-48c9f89a81e5
-- title:
--   An $n$-state two-way NFA for nonempty relation products whose complement needs at least $\frac12\cdot 2^{\lfloor (n-4)/127\rfloor}-1$ states
-- statement:
--   A two-way nondeterministic finite automaton (2NFA) $A$ over an alphabet $\Sigma$ with state set $Q$ consists of an initial state $q_0\in Q$, a set $F\subseteq Q$ of accepting states, and a transition map assigning to each state $q$ and each tape symbol $x\in\{\vdash,\dashv\}\sqcup\Sigma$ a set $\delta(q,x)\subseteq Q\times\{-1,0,+1\}$ of allowed pairs (next state, head move). A word $w=a_1\cdots a_m\in\Sigma^{*}$ is written on the tape $\vdash a_1\cdots a_m\dashv$ with cells $0,1,\dots,m+1$; the two distinct endmarkers $\vdash$ and $\dashv$ occupy cells $0$ and $m+1$, also for the empty word. A configuration is a pair $(q,k)$ of a state and a head position $k\in\{0,\dots,m+1\}$, and $(q,k)\to(q',k')$ is a step if $(q',k'-k)\in\delta(q,x_k)$, where $x_k$ is the symbol in cell $k$; a move that would take the head off the tape is not a step. The automaton accepts $w$ if some configuration whose state lies in $F$ is reachable from $(q_0,0)$ by a run of zero or more steps (no halting condition is imposed), and $L(A)\subseteq\Sigma^{*}$ denotes the set of accepted words.
--
--   For $h\in\mathbb{N}$ let $[h]=\{0,\dots,h-1\}$ and let $\Sigma_h$ be the finite alphabet whose letters are all binary relations $R\subseteq[h]\times[h]$. For a word $w=R_1\cdots R_m$ over $\Sigma_h$ let $\pi(w)=R_1R_2\cdots R_m$ be its relational product in path order, where $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, and where $\pi(\varepsilon)$ is the identity relation on $[h]$. The source language is
--
--   $$
--   \mathcal L_h=\{w\in\Sigma_h^{*}:\ \pi(w)\neq\varnothing\},
--   $$
--
--   the set of words admitting a chain $x_0,\dots,x_m\in[h]$ with $(x_{i-1},x_i)\in R_i$ for all $i$.
--
--   **Theorem.** Let $n\ge4$ be an integer. There is a 2NFA $A$ over $\Sigma_{n-2}$ with state set $[n]$, i.e. with exactly $n$ states, such that $L(A)=\mathcal L_{n-2}$ and such that for every finite set $Q$ and every 2NFA $B$ over $\Sigma_{n-2}$ with state set $Q$,
--
--   $$
--   L(B)=\Sigma_{n-2}^{*}\setminus L(A)\quad\Longrightarrow\quad |Q|\ \ge\ \frac12\cdot 2^{\lfloor (n-4)/127\rfloor}-1 .
--   $$
--
--   So an explicit $n$-state 2NFA, one that checks nonemptiness of relational products over $n-2$ points, has a complement whose 2NFAs all need a number of states exponential in $n/127$, whatever finite state set they use. Because the language of the witness is identified explicitly as $\mathcal L_{n-2}$, lower bounds for other kinds of automata recognizing $\mathcal L_{n-2}$, for instance deterministic two-way automata, apply to the same witness.
--
--   **Formalization Note** The alphabet is `SetRel (Fin (n - 2)) (Fin (n - 2))`, the witness is `A : TwoNFA _ (Fin n)` with `A.language = sourceLanguage (Fin (n - 2))`, and $B$ ranges over `TwoNFA _ Q` for every type `Q` with a `Fintype` instance, $|Q|$ being `Fintype.card Q`; the complement hypothesis is `B.language = A.languageᶜ`. Tape symbols are `Fin 2 ⊕ Sigma` with `Sum.inl 0` and `Sum.inl 1` as the endmarkers, and moves are coded `0, 1, 2` for left, stay, right. The exponent `(n - 4) / 127` is natural-number division (the floor), the subtractions do not truncate since $n\ge4$, and the inequality is stated in the real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/ExplicitFamily.lean#L7-L33

import Mathlib
import Definitions.Def_TwoWayDeterminization
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

open OAI OAI.TwoWayComplementation

theorem OAI.TwoWayComplementation.explicit_complementation_family (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) := by sorry
