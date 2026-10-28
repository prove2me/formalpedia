-- Prove2me | Theorems.Thm_OAI_Lech_FrobeniusGrowth_frobenius_error_tendstoENNReal
-- name    : OAI.Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:45:28.738882+00:00
-- url     : https://prove2.me/theorems/862d894b-bfce-44bc-9761-7bcb4b6ef3f6
-- title:
--   OAI.Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.FrobeniusGrowth`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open scoped nonZeroDivisors`, `open scoped BigOperators`, `open Filter`, `open scoped ENNReal Topology nonZeroDivisors`):
--
--   ```lean
--   lemma frobenius_error_tendstoENNReal (H : Ideal R)
--       (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰)
--       (p : ℕ) [Fact p.Prime] [CharP R p] :
--       Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension R))⁻¹ *
--         (Module.length R (R ⧸ (H.map (iterateFrobenius R p n) ⊔ Ideal.span {g}))).toENNReal)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proofs of `OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto`, `OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated` and `OAI.Lech.exists_frobenius_tensor_transfer` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain

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

namespace Lech.FrobeniusGrowth
open Filter
open scoped ENNReal Topology nonZeroDivisors
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma frobenius_error_tendstoENNReal (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰)
    (p : ℕ) [Fact p.Prime] [CharP R p] :
    Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension R))⁻¹ *
      (Module.length R (R ⧸ (H.map (iterateFrobenius R p n) ⊔ Ideal.span {g}))).toENNReal)
      atTop (𝓝 0) := by
  sorry
end Lech.FrobeniusGrowth

end
end

end OAI
end
