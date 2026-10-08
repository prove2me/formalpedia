-- Prove2me | Theorems.Thm_KarpPapadimitriou_Generator_theorem_2
-- name    : KarpPapadimitriou.Generator.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:27.305182+00:00
-- url     : https://prove2.me/theorems/a4467da3-bb11-482b-a0cc-bf21d35df791
-- title:
--   Theorem 2 — a small polynomial-time generator puts D(C) in P
-- statement:
--   Let $C$ be a combinatorial optimization problem and $G(C)$ a generator of violated inequalities. If every returned coefficient has the paper's uniform polynomial bound and the generator runs in polynomial time on its complete binary query code, then
--   $$D(C)\in\mathrm P.$$
--
--   Thus a sufficiently efficient separation procedure yields a deterministic polynomial-time decision procedure for the optimization problem's threshold language.
--
--   **Formalization Note** The generator must answer every rational query on every valid $z$, returning “O.K.” exactly on the rational convex hull, or an integer inequality both violated by the query and valid on all feasible points. Polynomial time is measured against the full code of $z$ and every reduced rational numerator and denominator.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 10, Theorem 2

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Oracle

namespace KarpPapadimitriou.Generator

/-- Theorem 2: a small polynomial-time generator makes the decision language polynomial-time
decidable. -/
theorem theorem_2 (C : COP) (gen : Oracle C)
    (hgen : IsGenerator C gen)
    (hsmall : IsSmallGenerator C gen)
    (hpoly : RunsInPolyTime C gen) :
    DLang C ∈ CookPvsNP.P Sym := by sorry

end KarpPapadimitriou.Generator
