-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_largeWitness_eventually
-- name    : OAI.YauCounterexamples.spherical_largeWitness_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:48:32.890562+00:00
-- url     : https://prove2.me/theorems/092bca75-fdb1-4e5b-b515-d50432a39fda
-- title:
--   OAI.YauCounterexamples.spherical_largeWitness_eventually: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_largeWitness_eventually` of [lean/OAI/Geometry/SmoothYau/Estimates/SphericalPinFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/SphericalPinFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   lemma spherical_largeWitness_eventually {P : Type*} [TopologicalSpace P]
--       (q : P → SmoothMetric (Euclidean 3) (Sphere 3))
--       (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
--         (chartAt (Euclidean 3) r).target) (a₀ : P) (k : ℕ) (hk : 3≤k)
--       (e : ℝ) (he : 0<e) (u : Sphere 3 → ℝ)
--       (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
--       (hue : ∀ x, -laplaceBeltrami (q a₀) u x=e*u x)
--       (hreg : SphericalRegular u) (hsimple : SphericalSimple (q a₀) u e)
--       (A B : ℝ) (hB : B<e) (hD : e<2*(k:ℝ)^2) (hscore : SphericalSignAbove u (A*(k:ℝ))) :
--       ∀ᶠ a in 𝓝 a₀, SphericalLargeWitness (q a) A B
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ContinuousSmoothFamilyOn`, `OAI.YauCounterexamples.SphericalRegular` and `OAI.YauCounterexamples.SphericalSignAbove` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.SphericalLargeWitness` and `OAI.YauCounterexamples.SphericalSimple` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere`, `OAI.YauCounterexamples.laplaceBeltrami` and `OAI.YauCounterexamples.metricCoefficients` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_fixed_witnesses` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/SphericalPinFormNorm.lean (declaration OAI.YauCounterexamples.spherical_largeWitness_eventually)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma spherical_largeWitness_eventually {P : Type*} [TopologicalSpace P]
    (q : P → SmoothMetric (Euclidean 3) (Sphere 3))
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt (Euclidean 3) r).target) (a₀ : P) (k : ℕ) (hk : 3≤k)
    (e : ℝ) (he : 0<e) (u : Sphere 3 → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x=e*u x)
    (hreg : SphericalRegular u) (hsimple : SphericalSimple (q a₀) u e)
    (A B : ℝ) (hB : B<e) (hD : e<2*(k:ℝ)^2) (hscore : SphericalSignAbove u (A*(k:ℝ))) :
    ∀ᶠ a in 𝓝 a₀, SphericalLargeWitness (q a) A B := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
