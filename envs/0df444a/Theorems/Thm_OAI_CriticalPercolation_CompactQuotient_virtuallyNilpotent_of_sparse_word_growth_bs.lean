-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_CompactQuotient_virtuallyNilpotent_of_sparse_word_growth_bs
-- name    : OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:31:58.741879+00:00
-- url     : https://prove2.me/theorems/c07a4ae6-2187-49b5-837b-5a98e0b42fcd
-- title:
--   OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth` of [lean/OAI/Probability/CriticalPercolation/Classification/DiscreteWeakGromovBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Classification/DiscreteWeakGromovBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.CompactQuotient`, with `open Set Function Topology`, `open scoped Classical Pointwise`):
--
--   ```lean
--   lemma virtuallyNilpotent_of_sparse_word_growth_bs {A : Type*} [Group A]
--       (hg : HasSparsePolynomialWordGrowth A) : Group.IsVirtuallyNilpotent A
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.CompactQuotient.HasSparsePolynomialWordGrowth` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Classification/DiscreteWeakGromovBridge.lean (declaration OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth)

import Mathlib
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.CompactQuotient
lemma virtuallyNilpotent_of_sparse_word_growth_bs {A : Type*} [Group A]
    (hg : HasSparsePolynomialWordGrowth A) : Group.IsVirtuallyNilpotent A := by
  sorry
end CriticalPercolation.CompactQuotient

end
end

end OAI
end
