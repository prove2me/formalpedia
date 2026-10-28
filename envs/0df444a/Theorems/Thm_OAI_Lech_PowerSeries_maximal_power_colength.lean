-- Prove2me | Theorems.Thm_OAI_Lech_PowerSeries_maximal_power_colength
-- name    : OAI.Lech.PowerSeries.maximal_power_colength
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:04:58.791375+00:00
-- url     : https://prove2.me/theorems/cfcf4379-ebf6-4c6a-a37e-1a58e82cb3df
-- title:
--   OAI.Lech.PowerSeries.maximal_power_colength: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PowerSeries`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open scoped nonZeroDivisors`, `open scoped BigOperators`, `open scoped nonZeroDivisors TensorProduct`, `open scoped Classical Pointwise`, `open CategoryTheory CategoryTheory.Limits`, `open CochainComplex CochainComplex.HomComplex`, `open scoped ENNReal ZeroObject`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows`, `open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian`, `open CategoryTheory`, `open MvPowerSeries IsLocalRing`):
--
--   ```lean
--   lemma maximal_power_colength (hh : 0 < h) (N : ℕ) (hN : 0 < N) :
--       Module.length (MvPowerSeries (Fin h) k)
--         (MvPowerSeries (Fin h) k ⧸ maximalIdeal (MvPowerSeries (Fin h) k)^N) =
--         ((N+h-1).choose h : ℕ)
--   ```
--
--   **Used by.** The proofs of `OAI.Lech.PowerSeries.finite_module_two_limits` and `OAI.Lech.PowerSeries.finite_module_two_limits_pos` of this split import it.
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
open MvPowerSeries IsLocalRing
variable {k : Type*} [Field k] (h : ℕ)

lemma maximal_power_colength (hh : 0 < h) (N : ℕ) (hN : 0 < N) :
    Module.length (MvPowerSeries (Fin h) k)
      (MvPowerSeries (Fin h) k ⧸ maximalIdeal (MvPowerSeries (Fin h) k)^N) =
      ((N+h-1).choose h : ℕ) := by
  sorry
end Lech.PowerSeries

end

end OAI
end
