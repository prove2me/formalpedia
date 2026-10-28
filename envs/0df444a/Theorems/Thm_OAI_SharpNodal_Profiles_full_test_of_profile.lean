-- Prove2me | Theorems.Thm_OAI_SharpNodal_Profiles_full_test_of_profile
-- name    : OAI.SharpNodal.Profiles.full_test_of_profile
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:13:25.858754+00:00
-- url     : https://prove2.me/theorems/7d9eaebd-5d48-4f9e-b801-0af1504433b2
-- title:
--   OAI.SharpNodal.Profiles.full_test_of_profile: intermediate lemma from OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpNodal.Profiles.full_test_of_profile` of [lean/OAI/Analysis/NodalLength/NodalLength/Subharmonic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/Subharmonic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpNodal.Profiles`, with `open scoped ContDiff Bundle ENNReal`, `open Bundle Manifold MeasureTheory`, `open scoped ContDiff ENNReal Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open Carleman`):
--
--   ```lean
--   theorem full_test_of_profile
--       {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
--       {B : ℕ → Plane} {S K e c : ℕ → ℝ} {Cp : ℝ}
--       (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
--       (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
--       (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
--       (hc : ∀ j, 0 < c j)
--       (hK : Tendsto (fun j => K j/(S j+‖B j‖)) atTop (𝓝 0))
--       (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
--       (he : Tendsto e atTop (𝓝 0))
--       (hpgrad : ∀ j i x, x∈Ω →
--         |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤e j)
--       (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
--       (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V) :
--       FullTestProperty Ω V
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpNodal.Carleman.euclideanLaplacian`, `OAI.SharpNodal.Profiles.FullTestProperty` and `OAI.SharpNodal.Profiles.WeightedProfileBounds` (definitions bundle `OAIQ4Nl000` of this split); `OAI.SharpNodal.Plane` and `OAI.SharpNodal.coordPartial` (the published bundle `Def_NodalLength`).
--
--   **Used by.** The proofs of `OAI.SharpNodal.Geometry.uniform_local_sup_lower`, `OAI.SharpNodal.Profiles.uniform_normalized_subdivision` and `OAI.SharpNodal.Profiles.uniform_persistence_alternative` of this split import it.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/Subharmonic.lean (declaration OAI.SharpNodal.Profiles.full_test_of_profile)

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section

attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem full_test_of_profile
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S K e c : ℕ → ℝ} {Cp : ℝ}
    (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0 < c j)
    (hK : Tendsto (fun j => K j/(S j+‖B j‖)) atTop (𝓝 0))
    (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x∈Ω →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤e j)
    (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V) :
    FullTestProperty Ω V := by
  sorry

end SharpNodal.Profiles

end
end
end

end OAI
end
