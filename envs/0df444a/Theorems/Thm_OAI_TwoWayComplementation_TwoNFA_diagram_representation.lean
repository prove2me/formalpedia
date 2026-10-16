-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_diagram_representation
-- name    : OAI.TwoWayComplementation.TwoNFA.diagram_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:10:53.955493+00:00
-- url     : https://prove2.me/theorems/37a1ef19-06c2-49e1-9926-62dec08c7e98
-- title:
--   Every $s$-state two-way NFA is recognized by a homomorphism into boundary diagrams on $s+1$ labels
-- statement:
--   A two-way nondeterministic finite automaton (2NFA) $A$ over an alphabet $\Sigma$ with state set $Q$ consists of an initial state $q_0\in Q$, a set $F\subseteq Q$ of accepting states and a transition map assigning to each state $q$ and each tape symbol $x\in\{\vdash,\dashv\}\sqcup\Sigma$ a set $\delta(q,x)\subseteq Q\times\{-1,0,+1\}$ of allowed pairs (next state, head move). A word $w=a_1\cdots a_n\in\Sigma^{*}$ is written on the tape $\vdash a_1\cdots a_n\dashv$ with cells $0,1,\dots,n+1$: the left endmarker $\vdash$ in cell $0$, the letter $a_k$ in cell $k$ and the right endmarker $\dashv$ in cell $n+1$. A configuration is a pair $(q,k)$ of a state $q$ and a head position $k\in\{0,\dots,n+1\}$, and $(q,k)\to(q',k')$ is a step if $(q',k'-k)\in\delta(q,x_k)$, where $x_k$ is the symbol in cell $k$; in particular the head never leaves the tape. The automaton accepts $w$ if some configuration whose state lies in $F$ is reachable from $(q_0,0)$ by a run of zero or more steps (no halting condition is imposed), and $L(A)\subseteq\Sigma^{*}$ denotes the set of accepted words.
--
--   For $m\in\mathbb{N}$ put $[m]=\{0,\dots,m-1\}$. A boundary diagram of size $m$ is a quadruple $D=(D_{\to},D_{\leftarrow},D_{\mathrm L},D_{\mathrm R})$ of binary relations on $[m]$. It is read as a summary of a block of tape whose two boundaries are crossed by paths carrying labels in $[m]$: $D_{\to}$ relates the label of a path entering on the left to the label with which it leaves on the right, $D_{\leftarrow}$ does the same from right to left, and $D_{\mathrm L}$, $D_{\mathrm R}$ record paths that enter and leave on the left, respectively on the right. Relations are composed in path order, $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\}$, $R^{*}$ denotes the reflexive–transitive closure of $R$ and $\Delta$ the identity relation. The product of two diagrams (glue the right boundary of $D$ to the left boundary of $E$) is
--
--   $$
--   \begin{aligned}
--   (DE)_{\to}&=D_{\to}\,(E_{\mathrm L}D_{\mathrm R})^{*}\,E_{\to}, &
--   (DE)_{\leftarrow}&=E_{\leftarrow}\,(D_{\mathrm R}E_{\mathrm L})^{*}\,D_{\leftarrow},\\
--   (DE)_{\mathrm L}&=D_{\mathrm L}\cup D_{\to}\,(E_{\mathrm L}D_{\mathrm R})^{*}\,E_{\mathrm L}\,D_{\leftarrow}, &
--   (DE)_{\mathrm R}&=E_{\mathrm R}\cup E_{\leftarrow}\,D_{\mathrm R}\,(E_{\mathrm L}D_{\mathrm R})^{*}\,E_{\to},
--   \end{aligned}
--   $$
--
--   with identity $I=(\Delta,\Delta,\varnothing,\varnothing)$; this product is associative, so the diagrams of size $m$ form a monoid.
--
--   **Theorem.** Let $\Sigma$ be an arbitrary alphabet, let $s\in\mathbb{N}$ and let $A$ be a 2NFA over $\Sigma$ with state set $[s]$. Then there exist a map $\tau$ from $\Sigma^{*}$ to the diagrams of size $s+1$, two diagrams $\lambda,\rho$ of size $s+1$ and two labels $a,b\in[s+1]$ such that
--
--   1. $\tau(\varepsilon)=I$ for the empty word $\varepsilon$;
--   2. $\tau(uv)=\tau(u)\,\tau(v)$ for all words $u,v\in\Sigma^{*}$;
--   3. for every word $w\in\Sigma^{*}$,
--   $$
--   w\in L(A)\iff (a,b)\in\bigl(\lambda\,\tau(w)\,\rho\bigr)_{\to}.
--   $$
--
--   Thus the language of an $s$-state 2NFA is recognized through a monoid homomorphism from the free monoid $\Sigma^{*}$ into the monoid of boundary diagrams on $s+1$ labels, by testing one fixed entry of the forward relation of the image framed by two fixed diagrams; one label more than the number of states suffices. This converts state lower bounds for two-way automata into lower bounds on the size of diagram monoids recognizing a language, and it is the bridge used to derive the exponential lower bound for complementing 2NFAs.
--
--   **Formalization Note** The automaton is `A : TwoNFA Sigma (Fin s)`; tape symbols are `Fin 2 ⊕ Sigma` with `Sum.inl 0` and `Sum.inl 1` the left and right endmarkers, and moves are coded `0, 1, 2` for left, stay, right. Diagrams are `Diagram (s + 1)` with fields `forward`, `backward`, `left`, `right` of type `SetRel (Fin (s + 1)) (Fin (s + 1))`; the product is `Diagram.comp` and $I$ is `Diagram.identity (s + 1)`. No finiteness of $\Sigma$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Representation.lean#L9-L79

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

theorem OAI.TwoWayComplementation.TwoNFA.diagram_representation {Sigma : Type*} {s : ℕ} (A : TwoNFA Sigma (Fin s)) :
    ∃ τ : List Sigma → Diagram (s + 1), ∃ l r : Diagram (s + 1), ∃ a b : Fin (s + 1),
      τ [] = Diagram.identity (s + 1) ∧
      (∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v)) ∧
      (∀ w, w ∈ A.language ↔ (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward) := by sorry
