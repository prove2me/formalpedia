-- Prove2me | Theorems.Thm_OAI_Lech_Normalization_parameter_multiplicity_pos
-- name    : OAI.Lech.Normalization.parameter_multiplicity_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:10:29.877024+00:00
-- url     : https://prove2.me/theorems/f36f245d-6f14-4738-9657-09106e5b1ffb
-- title:
--   OAI.Lech.Normalization.parameter_multiplicity_pos: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.Normalization`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open scoped nonZeroDivisors`, `open scoped BigOperators`, `open scoped nonZeroDivisors TensorProduct`, `open scoped Classical Pointwise`, `open CategoryTheory CategoryTheory.Limits`, `open CochainComplex CochainComplex.HomComplex`, `open scoped ENNReal ZeroObject`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows`, `open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian`, `open CategoryTheory`, `open IsLocalRing MvPowerSeries`):
--
--   ```lean
--   theorem parameter_multiplicity_pos (h : ℕ) (hh : 0 < h)
--       (hdim : Lech.dimension D = h) (φ : k →+* D)
--       (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
--       (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
--       0 < Lech.Primary.multiplicity (Ideal.span (Set.range z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.Primary.multiplicity` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.CharP.exists_length_with_module_limit` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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

namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

theorem parameter_multiplicity_pos (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    0 < Lech.Primary.multiplicity (Ideal.span (Set.range z)) := by
  sorry
end Lech.Normalization
end
end

end OAI
end
