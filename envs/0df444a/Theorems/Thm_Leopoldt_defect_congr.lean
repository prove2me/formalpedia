-- Prove2me | Theorems.Thm_Leopoldt_defect_congr
-- name    : Leopoldt.defect_congr
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:39:25.026456+00:00
-- url     : https://prove2.me/theorems/8f2eb93d-2c46-47f7-acd6-d2a748b319c4
-- title:
--   The Leopoldt defect is invariant under isomorphism
-- statement:
--   Let $p$ be a prime and let $K \cong L$ be isomorphic number fields. Then their Leopoldt defects at $p$ agree: $\mathcal{D}_L(K) = \mathcal{D}_L(L)$. In particular Leopoldt's conjecture for a number field depends only on its isomorphism class.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1, Remark 1.A (Leopoldt defect does not decrease in finite extensions); M. Laurent, Rang p-adique d'unités et action de groupes, J. reine angew. Math. 399 (1989), 81–108, Introduction. (Isomorphism invariance: apply Remark 1.A to the degree-one extensions L/K and K/L.)

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_congr (p : ℕ) [Fact p.Prime]
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) : defect p K = defect p L := by sorry
end Leopoldt
