-- Prove2me | Theorems.Thm_KarpPapadimitriou_Generator_facial_from_generator
-- name    : KarpPapadimitriou.Generator.facial_from_generator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:23.477268+00:00
-- url     : https://prove2.me/theorems/0a549ca0-0db1-4775-841f-973ba71969c2
-- title:
--   p. 9 — the output family of a generator is a facial description
-- statement:
--   Let $C$ be a combinatorial optimization problem and $G$ a generator that answers every valid rational query as specified. Then its returned inequalities form a facial description:
--   $$x\in\mathrm{CH}(S(z))\quad\Longleftrightarrow\quad f\cdot x\le g\text{ for every }\langle z,f,g\rangle\in F_G(C)$$
--   for each $z\in L$ and $x\in\mathbb Q^{n(z)}$.
--
--   This identifies the exact system of inequalities used by Theorem 2.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 9, paragraph defining F_G(C)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Oracle

namespace KarpPapadimitriou.Generator

/-- The output family of a generator describes precisely the convex hull. -/
theorem facial_from_generator (C : COP) (gen : Oracle C)
    (hgen : IsGenerator C gen) : IsFacialDescription C (FG C gen) := by sorry

end KarpPapadimitriou.Generator
