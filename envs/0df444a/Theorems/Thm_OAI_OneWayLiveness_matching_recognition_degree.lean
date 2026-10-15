-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_matching_recognition_degree
-- name    : OAI.OneWayLiveness.matching_recognition_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:28:16.182887+00:00
-- url     : https://prove2.me/theorems/7a958ea9-bf21-4474-b6e5-459be97bc5a3
-- title:
--   Recognising relational liveness by products of matching diagrams on $A\sqcup A$ requires $|A|\ge 2^{\lfloor (h-2)/31\rfloor}$
-- statement:
--   Let $\mathcal R_H$ denote the monoid of all binary relations on a set $H$, with product $RS=\{(x,z):\ (x,y)\in R \text{ and } (y,z)\in S \text{ for some } y\}$ (composition in diagrammatic order) and identity the diagonal $\Delta_H$. For $F\subseteq H$ write $\Delta_F=\{(z,z): z\in F\}$, and for $x,y\in H$ write $E_{x,y}=\Delta_H\cup\{(x,y)\}$ for the identity relation with one extra pair.
--
--   For a finite set $A$, let $\mathcal B_A$ be the Brauer monoid of $A$: an element is a perfect matching of the $2|A|$ ports $i_{\mathrm L},i_{\mathrm R}$ ($i\in A$), drawn with the left ports on one side and the right ports on the other; the product $\pi\sigma$ glues the right ports of $\pi$ to the left ports of $\sigma$, follows the resulting paths and discards closed loops, and the identity matches each $i_{\mathrm L}$ with $i_{\mathrm R}$. The rank $\operatorname{rk}\pi$ is the number of through strands, i.e. of $i\in A$ whose left port $i_{\mathrm L}$ is matched to some right port, and the support $\operatorname{supp}\pi$ is the set of $i\in A$ such that $i_{\mathrm L}$ is not matched to $i_{\mathrm R}$.
--
--   Let $H$ and $A$ be finite sets such that $H$ contains two distinct elements $x\neq y$. Let $\eta\colon\mathcal R_H\to\mathcal B_A$ be an arbitrary map (not necessarily a homomorphism) and $T$ an arbitrary property of diagrams in $\mathcal B_A$. Call a word $R_1R_2\cdots R_n$ over the alphabet $\mathcal R_H$ live if the relational product $R_1R_2\cdots R_n$ is nonempty, i.e. if there are $x_0,\dots,x_n\in H$ with $(x_{k-1},x_k)\in R_k$ for $1\le k\le n$. Assume that for every word (including the empty word, whose products are the identities $1$ and $\Delta_H$)
--
--   $$T\bigl(\eta(R_1)\,\eta(R_2)\cdots\eta(R_n)\bigr)\iff R_1R_2\cdots R_n\neq\varnothing .$$
--
--   Then
--
--   $$2^{\lfloor (|H|-2)/31\rfloor}\le|A| .$$
--
--   So any device that decides liveness by multiplying per-letter matching diagrams and testing the product needs $|A|$ exponentially large in $|H|$. Because the computation of a two-way deterministic automaton can be encoded by such diagrams with $|A|=4(\text{number of states}+1)^2$, this yields the state lower bound for the one-way liveness language.
--
--   **Formalization Note** The hypothesis is `∀ w : List (BRel H), test (w.map η).prod ↔ BRel.live w`, where `BRel.live w` means that some pair lies in `w.prod`. The types $H,A$ live in `Type`; the left-hand side of the conclusion is `rankLoss (Fintype.card H)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Syntactic.lean#L22-L55

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

open OAI OAI.OneWayLiveness
open scoped Classical

theorem OAI.OneWayLiveness.matching_recognition_degree {H A : Type} [Fintype H] [Fintype A]
    (η : BRel H → Pairing (A ⊕ A)) (test : Pairing (A ⊕ A) → Prop)
    (hη : ∀ w : List (BRel H), test (w.map η).prod ↔ BRel.live w)
    (x y : H) (hxy : x ≠ y) : rankLoss (Fintype.card H) ≤ Fintype.card A := by sorry
