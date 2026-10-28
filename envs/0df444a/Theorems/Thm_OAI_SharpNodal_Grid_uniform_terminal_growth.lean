-- Prove2me | Theorems.Thm_OAI_SharpNodal_Grid_uniform_terminal_growth
-- name    : OAI.SharpNodal.Grid.uniform_terminal_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:11:44.196886+00:00
-- url     : https://prove2.me/theorems/cb377d68-1dfe-45e0-a9c7-0adb1f754d4a
-- title:
--   OAI.SharpNodal.Grid.uniform_terminal_growth: intermediate lemma from OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpNodal.Grid.uniform_terminal_growth` of [lean/OAI/Analysis/NodalLength/NodalLength/TerminalGrid.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/TerminalGrid.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpNodal.Grid`, with `open scoped ContDiff Bundle ENNReal`, `open Bundle Manifold MeasureTheory`, `open scoped ContDiff ENNReal Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal NNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Set MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory Function`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Classical`, `open scoped BigOperators Topology ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Topology`, `open Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open Profiles`):
--
--   ```lean
--   theorem uniform_terminal_growth : ∃A : ℕ,10000<A ∧
--       ∀Cp : ℝ,0≤Cp → ∀a₀ : ℝ,0<a₀ → ∀Cinit : ℝ,
--       ∃C : ℝ,0≤C ∧ ∀(D : ScaledWave Cp a₀) (n : ℕ),
--         D.growth 0≤Cinit → a₀≤D.K/(A:ℝ)^n →
--         (𝔼 w : GridWord A n,pathGrowth A n D.U D.K w)≤C
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpNodal.Profiles.GridIndex`, `OAI.SharpNodal.Profiles.GridWord`, `OAI.SharpNodal.Profiles.ScaledWave`, `OAI.SharpNodal.Profiles.pathGrowth`, `OAI.SharpNodal.Profiles.UnitWave` and `OAI.SharpNodal.Profiles.UnitWave.growth` (definitions bundle `OAIQ4Nl000` of this split); `OAI.SharpNodal.Plane` (the published bundle `Def_NodalLength`).
--
--   **Used by.** The proofs of `OAI_SharpNodal_Geometry_exists_normalized_global_length` and `OAI.SharpNodal.Profiles.uniform_plane_length` of this split import it.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/TerminalGrid.lean (declaration OAI.SharpNodal.Grid.uniform_terminal_growth)

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section

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
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set

noncomputable section
open scoped BigOperators Classical
open Set
namespace SharpNodal.Grid
open Profiles

theorem uniform_terminal_growth : ∃A : ℕ,10000<A ∧
    ∀Cp : ℝ,0≤Cp → ∀a₀ : ℝ,0<a₀ → ∀Cinit : ℝ,
    ∃C : ℝ,0≤C ∧ ∀(D : ScaledWave Cp a₀) (n : ℕ),
      D.growth 0≤Cinit → a₀≤D.K/(A:ℝ)^n →
      (𝔼 w : GridWord A n,pathGrowth A n D.U D.K w)≤C := by
  sorry

end SharpNodal.Grid

end
end

end OAI
end
