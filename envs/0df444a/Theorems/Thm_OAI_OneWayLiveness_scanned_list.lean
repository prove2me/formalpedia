-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_scanned_list
-- name    : OAI.OneWayLiveness.scanned_list
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:28:50.666817+00:00
-- url     : https://prove2.me/theorems/23f27011-e24c-452d-8dcf-747bba75064e
-- title:
--   The tape of a word is the word framed by its two endmarkers
-- statement:
--   Let $\Sigma$ be any alphabet and $w=a_1\cdots a_n$ a word over $\Sigma$. A two-way automaton reads $w$ on a tape with $n+2$ cells numbered $0,\dots,n+1$; the symbol $\mathrm{scan}_w(k)$ in cell $k$ is the left endmarker $\vdash$ for $k=0$, the letter $a_k$ for $1\le k\le n$, and the right endmarker $\dashv$ for $k=n+1$. Then the list of scanned symbols, in order of the cells, is
--
--   $$\bigl(\mathrm{scan}_w(0),\mathrm{scan}_w(1),\dots,\mathrm{scan}_w(n+1)\bigr)=(\vdash,a_1,\dots,a_n,\dashv).$$
--
--   This identity lets the product of per-cell objects along the whole tape be split as (left endmarker part) times (product over the letters of $w$) times (right endmarker part); in the lower-bound argument it separates the diagrams of the two endmarkers from the letter diagrams.
--
--   **Formalization Note** The statement is `List.ofFn (scanned w) = Symbol.left :: (w.map Symbol.letter ++ [Symbol.right])`, where `scanned w : Fin (w.length + 2) → Symbol Alpha` is defined by cases on the cell index (index $0$, index below $n+1$, otherwise) and letters are indexed from $0$ in Lean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Recognition.lean#L8-L24

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

open OAI OAI.OneWayLiveness

theorem OAI.OneWayLiveness.scanned_list {Alpha : Type} (w : List Alpha) :
    List.ofFn (scanned w) = Symbol.left :: (w.map Symbol.letter ++ [Symbol.right]) := by sorry
