-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_of_finite
-- name    : Leopoldt.leopoldtConjecture_of_finite
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:39:28.964987+00:00
-- url     : https://prove2.me/theorems/7fac11f7-a93b-436e-af2b-72d0e25024d1
-- title:
--   Leopoldt's conjecture descends to subfields
-- statement:
--   Let $p$ be a prime and $K/F$ a finite extension of number fields. If Leopoldt's conjecture holds for $K$ at $p$ (i.e. $\mathcal{D}_L(K)=0$), then it holds for $F$ at $p$. This is the classical fact that Leopoldt's conjecture descends to subfields; it is immediate from $\mathcal{D}_L(F) \le \mathcal{D}_L(K)$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1, Remark 1.A (Leopoldt defect does not decrease in finite extensions); M. Laurent, Rang p-adique d'unités et action de groupes, J. reine angew. Math. 399 (1989), 81–108, Introduction. See also L. Washington, Introduction to Cyclotomic Fields, 2nd ed., §5.5.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldtConjecture_of_finite (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] :
    LeopoldtConjecture p K → LeopoldtConjecture p F := by sorry
end Leopoldt
