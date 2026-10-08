-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_corollary_1
-- name    : KarpPapadimitriou.Facial.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:29:07.500991+00:00
-- url     : https://prove2.me/theorems/4563fb0e-f068-4b28-b1f5-5b255639b760
-- title:
--   Corollary 1 — a small facial description in NP of an NP-complete c.o.p. gives NP = co-NP
-- statement:
--   Let $C$ be a combinatorial optimization problem whose decision problem $D(C)$ is NP-complete, and let $F(C)$ be a small facial description of $C$ with $F(C)\in\mathrm{NP}$. Then
--   $$\mathrm{NP}=\text{co-NP}.$$
--
--   This is the paper's evidence that computationally tractable facial descriptions of NP-complete combinatorial optimization problems are unlikely to exist.
--
--   **Formalization Note** NP-completeness is Cook's: $D(C)\in\mathrm{NP}$ and every NP language over every finite nonempty alphabet reduces to $D(C)$ in polynomial time. Accordingly the conclusion $\mathrm{NP}=\text{co-NP}$ is stated for every finite nonempty alphabet, since Cook's classes are indexed by the alphabet.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 8, Corollary 1

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

theorem corollary_1 (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (hNPC : NPComplete (DLang C)) (hNP : tripleLang C F ∈ NP BSym) :
    ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], NP Sym = coNP Sym := by sorry

end KarpPapadimitriou.Facial
