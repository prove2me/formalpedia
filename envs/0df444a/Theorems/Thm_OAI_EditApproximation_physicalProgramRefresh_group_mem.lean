-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalProgramRefresh_group_mem
-- name    : OAI.EditApproximation.physicalProgramRefresh_group_mem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:02.139337+00:00
-- url     : https://prove2.me/theorems/518ec468-d526-46c6-84e1-5030f67b8b5d
-- title:
--   OAI.EditApproximation.physicalProgramRefresh_group_mem: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalProgramRefresh_group_mem` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramRefreshWiring.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramRefreshWiring.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem physicalProgramRefresh_group_mem (draw : Draw) (fresh : Fresh)
--       (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent tau groupCell ≠ [])
--       (t : ℕ) :
--       (physicalNodeSelectedGroup source target U N P F A T delta (choices draw) node.1 node.2
--         b thetaExponent Q tau groupCell hnonempty t (parentGroupDraw fresh t)).rationalAction ∈
--         physicalNodeGroups source target U N P F A T delta
--           (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.physicalBandChildInitial` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.PhysicalGroupArray`, `OAI.EditApproximation.PhysicalOnlineArray`, `OAI.EditApproximation.PhysicalProgramDraw`, `OAI.EditApproximation.physicalBandChildMassTable`, `OAI.EditApproximation.physicalProgramBandK` and `OAI.EditApproximation.physicalProgramCells` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.parentGroupDraw` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.physicalNodeCellBands`, `OAI.EditApproximation.physicalNodeGroups`, `OAI.EditApproximation.physicalNodeSelectedGroup`, `OAI.EditApproximation.physicalProgramDrawSelections` and `OAI.EditApproximation.physicalProgramRefresh` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.RationalBellmanAction` and `OAI.EditApproximation.dyadicScales` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalInternalNode`, `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.TreeLayer` and `OAI.EditApproximation.optimizerTriangularMass` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.PhysicalRationalAction` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales` and `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.groupDyadicScaleAt` and `OAI.EditApproximation.UnskippedBand.rationalAction` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_conditional_node_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramRefreshWiring.lean (declaration OAI.EditApproximation.physicalProgramRefresh_group_mem)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section RefreshWiring

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau delta η κ : ℚ)
  (node : PhysicalInternalNode M J)
  (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
  (scale : Fin (dyadicScales N).length)
  (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).length)

local notation "onlineKey" => (Sigma.mk node representative : PhysicalOnlineKey source target U N P F A)
local notation "groupKey" => (Sigma.mk node (Sigma.mk scale cell) : PhysicalGroupKey source target U N P F A thetaExponent)
local notation "b" => List.get (dyadicScales N) scale
local notation "groupCell" => List.get (physicalProgramCells source target U N P F A thetaExponent (Subtype.val node) b) cell
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau

theorem physicalProgramRefresh_group_mem (draw : Draw) (fresh : Fresh)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent tau groupCell ≠ [])
    (t : ℕ) :
    (physicalNodeSelectedGroup source target U N P F A T delta (choices draw) node.1 node.2
      b thetaExponent Q tau groupCell hnonempty t (parentGroupDraw fresh t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t := by
  sorry

end RefreshWiring

end EditApproximation

end OAI
end
