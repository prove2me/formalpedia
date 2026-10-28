-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_HarmonicAnalysis_WordGeometry_exists_infinite_finiteDimensional_linear_image_bs
-- name    : OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:30:46.470846+00:00
-- url     : https://prove2.me/theorems/8f97cb10-2626-4a67-8f4f-fc121023eace
-- title:
--   OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image` of [lean/OAI/Probability/CriticalPercolation/Harmonic/HarmonicLinearQuotient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Harmonic/HarmonicLinearQuotient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry`, with `open Set Function`, `open scoped Classical Pointwise BigOperators`):
--
--   ```lean
--   theorem exists_infinite_finiteDimensional_linear_image_bs [Infinite A] (d : ℕ)
--       (hg : SparseGrowth.HasDegree W.generators d) :
--       ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V),
--         FiniteDimensional ℝ V ∧ ∃ ρ : A →* (V ≃ₗ[ℝ] V), (Set.range ρ).Infinite
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry` and `OAI.CriticalPercolation.SparseGrowth.HasDegree` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs` and `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Harmonic/HarmonicLinearQuotient.lean (declaration OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image)

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
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
universe u
variable {A : Type u} [Group A] (W : WordGeometry A)

theorem exists_infinite_finiteDimensional_linear_image_bs [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V),
      FiniteDimensional ℝ V ∧ ∃ ρ : A →* (V ≃ₗ[ℝ] V), (Set.range ρ).Infinite := by
  sorry

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end
