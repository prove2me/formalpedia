-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_reindex_language
-- name    : OAI.TwoWayComplementation.TwoNFA.reindex_language
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:55:31.695989+00:00
-- url     : https://prove2.me/theorems/7b027931-211b-4249-a3ff-c35990f1be5a
-- title:
--   Renaming the states of a two-way nondeterministic automaton preserves its language
-- statement:
--   Let $\Sigma$ be an alphabet and let $A=(Q,q_0,F,\delta)$ be a two-way nondeterministic automaton over $\Sigma$: $Q$ is an arbitrary set of states, $q_0\in Q$ is the initial state, $F\subseteq Q$ is the set of accepting states, and $\delta$ assigns to every state $q$ and every tape symbol $b\in\{\vdash,\dashv\}\sqcup\Sigma$ a set $\delta(q,b)\subseteq Q\times\{L,S,R\}$ of pairs (next state, head move). A word $w=a_1\cdots a_n\in\Sigma^*$ is written on the tape positions $0,1,\dots,n+1$ as $\vdash a_1\cdots a_n\dashv$, and $b_i$ denotes the symbol at position $i$. A configuration is a pair $(q,i)$ with $q\in Q$ and $0\le i\le n+1$, and $(q,i)\to(q',j)$ is a step if $(q',\mu)\in\delta(q,b_i)$ and $j=i+\Delta(\mu)$, where $\Delta(L)=-1$, $\Delta(S)=0$, $\Delta(R)=1$; a move that would leave the tape is not a step. The language $\mathcal{L}(A)$ is the set of words $w$ for which some configuration with an accepting state is reachable from $(q_0,0)$ by finitely many steps, possibly none; $\to^{*}$ denotes this reachability.
--
--   Now let $e:Q\to Q'$ be a bijection onto a set $Q'$, and let $A^{e}$ be the automaton with state set $Q'$, initial state $e(q_0)$, accepting set $e(F)$ and transitions
--   $$
--   \delta^{e}(q',b)=\bigl\{(e(r),\mu)\ :\ (r,\mu)\in\delta(e^{-1}(q'),b)\bigr\}\qquad\bigl(q'\in Q',\ b\in\{\vdash,\dashv\}\sqcup\Sigma\bigr).
--   $$
--   Then
--   $$
--   \mathcal{L}(A^{e})=\mathcal{L}(A).
--   $$
--
--   Thus the language of a two-way automaton depends on its state set only up to renaming. This is used to move automata onto standard numbered state sets $\{0,1,\dots,s-1\}$: the automaton recognizing the words of relations on a finite set $H$ with nonempty product, built on the states $\{q_{\mathrm{st}},q_{\mathrm{acc}}\}\sqcup H$, is moved onto $|H|+2$ numbered states, and a complement automaton with an arbitrary finite state set $Q$ is moved onto $|Q|$ numbered states before the diagram argument is applied.
--
--   **Formalization Note** `TwoNFA Sigma Q` has fields `initial`, `accepting` and `transition`; tape symbols are `Fin 2 ⊕ Sigma` with `Sum.inl 0` and `Sum.inl 1` the endmarkers $\vdash$ and $\dashv$ (read by `tapeSymbol w`), the moves $L,S,R$ are `0, 1, 2 : Fin 3` with displacement `move.val - 1` computed in the integers, configurations are `Q × Fin (w.length + 2)`, the step relation is `A.step w`, and reachability is `relStar`, the reflexive–transitive closure. The automaton $A^{e}$ is `A.reindex e` for `e : Q ≃ Q'`; its accepting set is written as the preimage `e.symm ⁻¹' A.accepting`, which is $e(F)$, and its transition set at `q'` consists of the pairs whose state, pulled back by `e.symm`, forms with the same move an element of `A.transition (e.symm q') b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean#L29-L44

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

theorem OAI.TwoWayComplementation.TwoNFA.reindex_language {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') :
    (A.reindex e).language = A.language := by sorry
