-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_marked_getElem
-- name    : OAI.TwoWayComplementation.marked_getElem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:08:04.305755+00:00
-- url     : https://prove2.me/theorems/06316b4d-9761-4689-add4-04c2474a1bb4
-- title:
--   Reading the marked word $\vdash w\dashv$ at index $p$ gives the tape symbol at position $p$
-- statement:
--   Let $\Sigma$ be an alphabet and $w=a_1a_2\cdots a_n\in\Sigma^*$. The tape of a two-way automaton on input $w$ has positions $0,1,\dots,n+1$, and its symbol at position $p$ is
--   $$
--   b_p=\begin{cases}\vdash, & p=0,\\ \dashv, & p=n+1,\\ a_p, & 1\le p\le n,\end{cases}
--   $$
--   an element of the extended alphabet $\{\vdash,\dashv\}\sqcup\Sigma$. Over this alphabet form the marked list $\vdash a_1\cdots a_n\dashv$ of length $n+2$, indexed from $0$. Then for every $p\in\{0,1,\dots,n+1\}$
--   $$
--   \bigl(\vdash a_1\cdots a_n\dashv\bigr)[p]=b_p .
--   $$
--
--   So the case-defined tape lookup agrees with ordinary list indexing of the explicitly marked word. This lets the cells $\vdash,a_1,\dots,a_n$ followed by the final cell $\dashv$ of a chain of cell networks be identified with the tape of a two-way automaton, position by position.
--
--   **Formalization Note** The tape symbol is `tapeSymbol w p` for `p : Fin (w.length + 2)`, equal to `Sum.inl 0` ($\vdash$) if `p = 0`, to `Sum.inl 1` ($\dashv$) if `p = w.length + 1`, and to `Sum.inr w[p - 1]` otherwise. The marked list is `Sum.inl 0 :: (w.map Sum.inr ++ [Sum.inl 1])`, read with the 0-based index `p.val`; Lean lists are 0-based, so $a_p$ is `w[p - 1]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean#L25-L39

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

theorem OAI.TwoWayComplementation.marked_getElem {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    ((Sum.inl 0 : Fin 2 ⊕ Sigma) :: (w.map Sum.inr ++ [Sum.inl 1]))[p.val]'(by simp; omega) =
      tapeSymbol w p := by sorry
