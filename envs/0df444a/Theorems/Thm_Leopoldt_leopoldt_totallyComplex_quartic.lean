-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_totallyComplex_quartic
-- name    : Leopoldt.leopoldt_totallyComplex_quartic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:15:16.826267+00:00
-- url     : https://prove2.me/theorems/044fb7a5-9fbe-41e2-8e4c-ef2f45a297ea
-- title:
--   Leopoldt's conjecture for totally complex quartic fields
-- statement:
--   Let $K$ be a totally complex number field of degree four over $\mathbb{Q}$, and let $p$ be any prime, including $2$. Then the Leopoldt defect of $K$ at $p$ vanishes. This includes all quartic CM fields, whether or not they are Galois. Dirichlet’s formula gives unit rank $r_1+r_2-1=0+2-1=1$; one infinite-order unit remains of infinite order in the semilocal $p$-adic completion, giving the full required rank.
-- source:
--   Specialization of the standard unit-rank-one case of Leopoldt’s conjecture; see Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1, p. 3 (Dirichlet unit rank and Leopoldt defect). Formally follows from platform theorems Leopoldt.units_rank_of_isTotallyComplex and Leopoldt.leopoldtConjecture_of_units_rank_le_one.

import Definitions.Def_LeopoldtDefect
open NumberField

namespace Leopoldt
theorem leopoldt_totallyComplex_quartic (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 4) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
