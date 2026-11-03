-- Prove2me | Theorems.Thm_GeneratesNS_three_two_kernel_poly_growth
-- name    : GeneratesNS.three_two_kernel_poly_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T17:58:29.765417+00:00
-- url     : https://prove2.me/theorems/b06c958f-f96d-45b4-bdee-dae6ff72ddbb
-- title:
--   GeneratesNS.three_two_kernel_poly_growth: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `GeneratesNS`, with `open Subgroup`, `open scoped Finset`, `open scoped Pointwise`, `open scoped commutatorElement`, `open Generates`, `open scoped RealInnerProductSpace`, `open MeasureTheory`, `open Additive`):
--
--   ```lean
--   lemma three_two_kernel_poly_growth  (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1)
--    : HasPolynomialGrowthD (G := Multiplicative φ.ker) (d - 1) (S := (S_n_ker_phi S φ γ hγ n) ∪ (S_n_ker_phi S φ γ hγ n)⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `Generates`, `HasPolynomialGrowthD`, `GeneratesNS.G_dec_eq` and `GeneratesNS.G_group` (definitions bundle `OAIQ093D000` of this split); `GeneratesNS.S_n_ker_phi` (definitions bundle `OAIQ093D016` of this split).
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D016

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

lemma three_two_kernel_poly_growth  (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1)
 : HasPolynomialGrowthD (G := Multiplicative φ.ker) (d - 1) (S := (S_n_ker_phi S φ γ hγ n) ∪ (S_n_ker_phi S φ γ hγ n)⁻¹) := by
  sorry

end GeneratesNS
end
