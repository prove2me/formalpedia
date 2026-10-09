-- Prove2me | Theorems.Thm_OAI_Erdos3_affineCommonReferenceBudget_bounds
-- name    : OAI.Erdos3.affineCommonReferenceBudget_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:33.534188+00:00
-- url     : https://prove2.me/theorems/567c1065-4a07-41f6-9f44-0d679531e3ce
-- title:
--   The common affine reference budget is nonnegative and dominates U and the reference degree
-- statement:
--   Let $E$ be a natural number with $2 \le E$, let $\varepsilon$ be any real number, and let $U$ be a real number with $0 \le U$. Write $\beta = $ `affineCommonReferenceBudget E ε U` $= 2\,(\texttt{affineReferenceInput}\ \varepsilon\ U + 2)^E$, where `affineReferenceInput ε U` is an explicit real-valued function of OpenAI. Then $0 \le \beta$, $U \le \beta$, and $\lceil (\texttt{affineReferenceInput}\ \varepsilon\ U + 2)^E \rceil \le \beta$, the ceiling being the natural-number ceiling cast to $\mathbb{R}$.
--
--   Lean: `OAI.Erdos3.affineCommonReferenceBudget_bounds` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineCommonReferenceBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineCommonReferenceBudget.lean#L61

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem affineCommonReferenceBudget_bounds {E : ℕ} (hE : 2 ≤ E) (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ affineCommonReferenceBudget E epsilon U ∧
    U ≤ affineCommonReferenceBudget E epsilon U ∧
    (⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ : ℝ) ≤ affineCommonReferenceBudget E epsilon U := by
  sorry

end Erdos3
end
end OAI
