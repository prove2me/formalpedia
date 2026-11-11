-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_surface_configuration_outside_countable_closed_s01
-- name    : OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:29.914353+00:00
-- url     : https://prove2.me/theorems/7c34e316-1a2c-479c-b7ba-646d97f3b90b
-- title:
--   OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed` of [lean/OAI/AlgebraicGeometry/Seshadri/Configurations/Configurations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Configurations/Configurations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace`, `open scoped AlgebraicGeometry`):
--
--   ```lean
--   theorem surface_configuration_outside_countable_closed_s01
--       (S : Surface) (r : ℕ) (Z : ℕ → Set (Configuration S r))
--       (hclosed : ∀ k, IsClosed (Z k)) (hproper : ∀ k, Z k ≠ Set.univ) :
--       ∃ p : Configuration S r, ∀ k, p ∉ Z k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.Surface` and `OAI.MaximalSeshadri.Geometry.configurationTopology` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Configurations/Configurations.lean (declaration OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem surface_configuration_outside_countable_closed_s01
    (S : Surface) (r : ℕ) (Z : ℕ → Set (Configuration S r))
    (hclosed : ∀ k, IsClosed (Z k)) (hproper : ∀ k, Z k ≠ Set.univ) :
    ∃ p : Configuration S r, ∀ k, p ∉ Z k := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
