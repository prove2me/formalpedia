-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Interpolation_eventual_torus_jet_test_s01
-- name    : OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:26.400204+00:00
-- url     : https://prove2.me/theorems/4cb83298-2bba-4dc6-b61e-8e1f855dbedf
-- title:
--   OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test` of [lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/TorusJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/TorusJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Interpolation`, with `open scoped BigOperators Pointwise`):
--
--   ```lean
--   theorem eventual_torus_jet_test_s01 (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T) :
--       ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
--         ∃ t : ℝ, T < t ∧ ∃ points : Fin r → ℂ × ℂ,
--           Function.Injective points ∧ (∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0) ∧
--           ∀ (k m : ℕ), 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
--             ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
--               (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t) →
--               ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
--                 ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Interpolation.MixedJetZero`, `OAI.MaximalSeshadri.Interpolation.compressedTriangle` and `OAI.MaximalSeshadri.Interpolation.laurentEval` (definitions bundle `Q223SES002` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/TorusJets.lean (declaration OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test)

import Mathlib
import Definitions.Def_Q223SES002

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

theorem eventual_torus_jet_test_s01 (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ t : ℝ, T < t ∧ ∃ points : Fin r → ℂ × ℂ,
        Function.Injective points ∧ (∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0) ∧
        ∀ (k m : ℕ), 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
          ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
            (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t) →
            ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
              ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m := by
  sorry

open scoped BigOperators ContDiff
open Filter Topology

end MaximalSeshadri.Interpolation
end

end OAI
end
