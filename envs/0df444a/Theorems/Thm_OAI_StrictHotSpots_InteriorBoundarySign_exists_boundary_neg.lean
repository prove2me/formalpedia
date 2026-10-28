-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_InteriorBoundarySign_exists_boundary_neg
-- name    : OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:11:46.719403+00:00
-- url     : https://prove2.me/theorems/68881fbd-11fc-4a9e-8e41-a4c1fceee413
-- title:
--   OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg` of [lean/OAI/Analysis/HotSpots/HotSpots/Multiplicity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplicity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.InteriorBoundarySign`, with `open Set Filter MeasureTheory`, `open scoped Topology ContDiff InnerProductSpace ENNReal`, `open StrictHotSpots.BoundarySign`):
--
--   ```lean
--   lemma exists_boundary_neg (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
--       (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω)) (hne : ∃ x ∈ Ω, u x ≠ 0) :
--       ∃ x ∈ frontier Ω, u x < 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.InInteriorNeumannEigenspace` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplicity.lean (declaration OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorBoundarySign

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.InteriorBoundarySign
open StrictHotSpots.BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
lemma exists_boundary_neg (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω)) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∃ x ∈ frontier Ω, u x < 0 := by
  sorry

end StrictHotSpots.InteriorBoundarySign
end
end ActualInteriorBoundarySign

end OAI
end
