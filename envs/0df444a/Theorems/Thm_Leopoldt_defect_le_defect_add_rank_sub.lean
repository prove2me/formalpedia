-- Prove2me | Theorems.Thm_Leopoldt_defect_le_defect_add_rank_sub
-- name    : Leopoldt.defect_le_defect_add_rank_sub
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:39:23.528984+00:00
-- url     : https://prove2.me/theorems/2d3988e1-75ed-4411-920f-3364303eede5
-- title:
--   Upper bound for the Leopoldt defect in a finite extension
-- statement:
--   Let $p$ be a prime and $K/F$ a finite extension of number fields, with unit ranks $r_F = \mathbb{Z}\text{-rk}(E_F)$ and $r_K$. Then $$\mathcal{D}_L(K) \le \mathcal{D}_L(F) + (r_K - r_F).$$ This follows because the $\mathbb{Z}_p$-rank of the $p$-adic closure $\overline{E}$ of the units can only increase from $F$ to $K$ (the map of semilocal units $U_F \to U_K$ is continuous and injective and carries $\overline{E}_F$ into $\overline{E}_K$), and $r_F \le r_K$. (Here the subtraction $r_K - r_F$ is honest since $r_F \le r_K$.)
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1, Remark 1.A (Leopoldt defect does not decrease in finite extensions); M. Laurent, Rang p-adique d'unités et action de groupes, J. reine angew. Math. 399 (1989), 81–108, Introduction. Complementary to Remark 1.A: the defect grows by at most the growth of the unit rank.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_le_defect_add_rank_sub (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] :
    defect p K ≤ defect p F + (Units.rank K - Units.rank F) := by sorry
end Leopoldt
