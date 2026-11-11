-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_disk_nonlinear_jet_cauchy_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:20:32.43952+00:00
-- url     : https://prove2.me/theorems/d5b90fec-43db-49e0-9d70-d4dda32fef3b
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy` of [lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   theorem disk_nonlinear_jet_cauchy_bp240 {L H : ℝ} (hL : 0≤L) (hH : 0≤H) :
--       ∃ δ : ℝ,0<δ ∧ ∀ (u : ℕ → ℂ → E) (hu : ∀ i,ContDiff ℝ ∞ (u i))
--         (F : ℕ → E → E →L[ℝ] E),
--         (∀ i,Continuous (F i)) →(∀ i,F i 0=0) →
--         (∀ i x y,‖F i x-F i y‖≤L*‖x-y‖) →(∀ i,u i 0=0) →
--         (∀ i z,‖z‖≤2 →‖u i z‖≤δ) →
--         (∀ i z,‖z‖≤2 →‖fderiv ℝ (u i) z‖≤H) →
--         (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →‖u i z-u j z‖≤ε) →
--         (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ v,‖v‖≤δ →‖F i v-F j v‖≤ε) →
--         (∀ i z,‖z‖<2 →fderiv ℝ (u i) z Complex.I-Complex.I • fderiv ℝ (u i) z 1=
--           F i (u i z) (fderiv ℝ (u i) z 1)) →
--         CauchySeq (fun i => cutoffCurveJet smallDiskBump (hu i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smallDiskBump` (definitions bundle `OAIQ240Bp002` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet` (definitions bundle `OAIQ240Bp008` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy)

import Mathlib
import Definitions.Def_OAIQ240Bp008

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.djcInst1
local instance djcInst2_re488fd_1 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance djcInst3_re488fd_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance djcInst4_re488fd_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
theorem disk_nonlinear_jet_cauchy_bp240 {L H : ℝ} (hL : 0≤L) (hH : 0≤H) :
    ∃ δ : ℝ,0<δ ∧ ∀ (u : ℕ → ℂ → E) (hu : ∀ i,ContDiff ℝ ∞ (u i))
      (F : ℕ → E → E →L[ℝ] E),
      (∀ i,Continuous (F i)) →(∀ i,F i 0=0) →
      (∀ i x y,‖F i x-F i y‖≤L*‖x-y‖) →(∀ i,u i 0=0) →
      (∀ i z,‖z‖≤2 →‖u i z‖≤δ) →
      (∀ i z,‖z‖≤2 →‖fderiv ℝ (u i) z‖≤H) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →‖u i z-u j z‖≤ε) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ v,‖v‖≤δ →‖F i v-F j v‖≤ε) →
      (∀ i z,‖z‖<2 →fderiv ℝ (u i) z Complex.I-Complex.I • fderiv ℝ (u i) z 1=
        F i (u i z) (fderiv ℝ (u i) z 1)) →
      CauchySeq (fun i => cutoffCurveJet smallDiskBump (hu i)) := by
  sorry

end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
