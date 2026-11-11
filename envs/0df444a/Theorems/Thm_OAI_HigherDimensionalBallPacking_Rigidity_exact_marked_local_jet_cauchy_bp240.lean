-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_local_jet_cauchy_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:49:33.585307+00:00
-- url     : https://prove2.me/theorems/f7c6f9bf-e954-4e01-9c38-c48d98a9143c
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy` of [lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`, `open HolderCompletion`, `open scoped BoundedContinuousFunction`):
--
--   ```lean
--   theorem exact_marked_local_jet_cauchy_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1)
--       (hout : ∀ x,S < capacity x →J x=standardJ n)
--       {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
--       {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
--       {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i))
--       {v : ℂ → Phase n} (huc : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) :
--       ∃ r : ℝ,0 < r ∧ r≤1 ∧ ∀ c : ℂ,
--         CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i).1 c r))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.PseudoHolomorphicAt`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smallDiskBump` (definitions bundle `OAIQ240Bp002` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet` (definitions bundle `OAIQ240Bp008` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.eljcInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.eljcInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.markedLocalCurve` and `OAI.HigherDimensionalBallPacking.Rigidity.markedLocalCurve_smooth` (definitions bundle `OAIQ240Bp019` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp019

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst2
local instance eljcInst3_rc2c901_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance eljcInst4_rc2c901_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
theorem exact_marked_local_jet_cauchy_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i))
    {v : ℂ → Phase n} (huc : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) :
    ∃ r : ℝ,0 < r ∧ r≤1 ∧ ∀ c : ℂ,
      CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i).1 c r)) := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
