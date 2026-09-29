-- Prove2me | Theorems.Thm_Leopoldt_defect_le_defect_of_finite
-- name    : Leopoldt.defect_le_defect_of_finite
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:39:37.313996+00:00
-- url     : https://prove2.me/theorems/78edb27b-6234-4811-9c48-efb9a7267aec
-- title:
--   The Leopoldt defect does not decrease in finite extensions
-- statement:
--   Let $p$ be a prime and let $K/F$ be a finite extension of number fields. Then the Leopoldt defect does not decrease: $$\mathcal{D}_L(F) \le \mathcal{D}_L(K),$$ where $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E_K) - \mathbb{Z}_p\text{-rk}(\overline{E}_K)$ is the difference between the Dirichlet unit rank and the $\mathbb{Z}_p$-rank of the $p$-adic closure of the global units in the semilocal units at $p$. Equivalently: if Leopoldt's conjecture fails for $F$, it fails for every finite extension $K$ of $F$ (the numerical form of Remark 1.A of Mihăilescu).
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1, Remark 1.A (Leopoldt defect does not decrease in finite extensions); M. Laurent, Rang p-adique d'unités et action de groupes, J. reine angew. Math. 399 (1989), 81–108, Introduction.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_le_defect_of_finite (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] :
    defect p F ≤ defect p K := by sorry
end Leopoldt
