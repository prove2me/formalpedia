-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_theorem_1
-- name    : KarpPapadimitriou.Facial.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:29:12.874985+00:00
-- url     : https://prove2.me/theorems/b87871ea-2ece-4bcb-a81b-00b4177b00ec
-- title:
--   Theorem 1 — a small facial description in NP puts D(C) in co-NP
-- statement:
--   Let $C$ be a combinatorial optimization problem and let $F(C)$ be a small facial description of $C$. If $F(C)\in\mathrm{NP}$, then
--   $$D(C)\in\text{co-NP}.$$
--
--   Here $F(C)\in\mathrm{NP}$ means that the language of codes $\langle z,f,g\rangle$ of the triples of $F(C)$ is in NP, and $D(C)\in$ co-NP means that the complement of the language $D(C)$, taken over all strings of the alphabet (including strings that encode no triple $\langle z,c,k\rangle$), is in NP.
--
--   This is the main result of Karp and Papadimitriou. Since $D(C)$ is NP-complete for most classical combinatorial optimization problems, it says that such problems admit no linear description of their polytopes with polynomially sized coefficients and polynomially checkable membership, unless NP = co-NP.
--
--   **Formalization Note** P, NP and co-NP are Cook's classes (deterministic one-tape Turing machines, time bound $|w|^k+k$), over the alphabet $\{0,1,-,\#\}$ with integers in binary. No hypothesis $S(z)\neq\emptyset$ is made; the statement covers empty feasible sets as the paper does.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 7, Theorem 1

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1 (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (hNP : tripleLang C F ∈ NP BSym) :
    DLang C ∈ coNP BSym := by sorry

end KarpPapadimitriou.Facial
