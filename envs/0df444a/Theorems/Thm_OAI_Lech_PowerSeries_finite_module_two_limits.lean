-- Prove2me | Theorems.Thm_OAI_Lech_PowerSeries_finite_module_two_limits
-- name    : OAI.Lech.PowerSeries.finite_module_two_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:04:37.470769+00:00
-- url     : https://prove2.me/theorems/854bac64-661b-43da-af8a-a539cb06a0b2
-- title:
--   OAI.Lech.PowerSeries.finite_module_two_limits: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PowerSeries`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open scoped nonZeroDivisors`, `open scoped BigOperators`, `open scoped nonZeroDivisors TensorProduct`, `open scoped Classical Pointwise`, `open CategoryTheory CategoryTheory.Limits`, `open CochainComplex CochainComplex.HomComplex`, `open scoped ENNReal ZeroObject`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows`, `open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian`, `open CategoryTheory`, `open MvPowerSeries IsLocalRing Filter`, `open scoped Topology nonZeroDivisors`):
--
--   ```lean
--   theorem finite_module_two_limits (h : ℕ) (hh : 0 < h) (M : Type*) [AddCommGroup M]
--       [Module (MvPowerSeries (Fin h) k) M] [Module.Finite (MvPowerSeries (Fin h) k) M] :
--       ∃ n : ℕ,
--         Tendsto (fun q : ℕ => (h.factorial : ℝ) *
--           ((Module.length (MvPowerSeries (Fin h) k)
--             (M ⧸ (maximalIdeal (MvPowerSeries (Fin h) k))^q • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) / (q : ℝ)^h)
--           atTop (𝓝 (n : ℝ)) ∧
--         Tendsto (fun q : ℕ =>
--           ((Module.length (MvPowerSeries (Fin h) k)
--             (M ⧸ Ideal.span (Set.range (fun i : Fin h => (X i : MvPowerSeries (Fin h) k)^q)) • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) /
--             (q : ℝ)^h) atTop (𝓝 (n : ℝ))
--   ```
--
--   **Used by.** The proof of `OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology nonZeroDivisors
variable {k : Type*} [Field k]

theorem finite_module_two_limits (h : ℕ) (hh : 0 < h) (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries (Fin h) k) M] [Module.Finite (MvPowerSeries (Fin h) k) M] :
    ∃ n : ℕ,
      Tendsto (fun q : ℕ => (h.factorial : ℝ) *
        ((Module.length (MvPowerSeries (Fin h) k)
          (M ⧸ (maximalIdeal (MvPowerSeries (Fin h) k))^q • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) / (q : ℝ)^h)
        atTop (𝓝 (n : ℝ)) ∧
      Tendsto (fun q : ℕ =>
        ((Module.length (MvPowerSeries (Fin h) k)
          (M ⧸ Ideal.span (Set.range (fun i : Fin h => (X i : MvPowerSeries (Fin h) k)^q)) • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) /
          (q : ℝ)^h) atTop (𝓝 (n : ℝ)) := by
  sorry

end Lech.PowerSeries

end

end OAI
end
