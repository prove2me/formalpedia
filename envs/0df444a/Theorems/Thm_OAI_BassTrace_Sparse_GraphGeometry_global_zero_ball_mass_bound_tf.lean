-- Prove2me | Theorems.Thm_OAI_BassTrace_Sparse_GraphGeometry_global_zero_ball_mass_bound_tf
-- name    : OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound_tf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:08:37.316387+00:00
-- url     : https://prove2.me/theorems/fa5e6754-43ce-41f8-bf6d-85dec7f6ba25
-- title:
--   OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound_tf: intermediate lemma from OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TorsionFreeBass.torsion_free_corollary`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound` of [lean/OAI/RingTheory/BassTrace/BallMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/BallMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BassTrace.Sparse.GraphGeometry`, with `open Set MeasureTheory`, `open Finset MeasureTheory intervalIntegral`, `open Set Finset MeasureTheory`, `open scoped BassTrace.Sparse Classical ENNReal`):
--
--   ```lean
--   theorem global_zero_ball_mass_bound_tf (μ : Measure X) [IsFiniteMeasure μ]
--       (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
--       {R : ℝ} (hR : 0<R) (c : FinProbability Y) (hc : c.coeff.support.card≤n+1)
--       (r : ℝ) (hr : 0 ≤ r) (hrR : r≤R)
--       (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
--       (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
--       ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
--         ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
--           (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
--           (realizationDistance Γ hΓ K n) R n,
--         Q.NearMinimal (realizationDistance Γ hΓ K n) R
--           (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
--         (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r).toReal≤C*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.BassTrace.Sparse.FinProbability`, `OAI.BassTrace.Sparse.SourceTop`, `OAI.BassTrace.Sparse.GraphGeometry.graphMetric`, `OAI.BassTrace.Sparse.GraphGeometry.realizationDistance`, `OAI.BassTrace.Sparse.OrbitForms.MarkedPair` and `OAI.BassTrace.Sparse.OrbitForms.SeparatingFiltration` (definitions bundle `OAIQ113B000` of this split); `OAI.BassTrace.Sparse.dividedPower` and `OAI.BassTrace.Sparse.OrbitAreas.orbitReps` (definitions bundle `OAIQ113B001` of this split); `OAI.BassTrace.Sparse.normalizedArea`, `OAI.BassTrace.Sparse.GraphGeometry.ballMass`, `OAI.BassTrace.Sparse.GraphGeometry.ballVolumeBound`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_4` and `OAI.BassTrace.Sparse.OrbitForms.SeparatingFiltration.NearMinimal` (definitions bundle `OAIQ113B002` of this split).
--
--   **Used by.** The proofs of `OAI.TorsionFreeBass.scalar_trace_eq_augmentation_tf` and `OAI.TorsionFreeBass.torsion_free_corollary` of this split import it.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/BallMass.lean (declaration OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound)

import Mathlib
import Definitions.Def_OAIQ113B002

section

attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_4
local instance instCountableSourceTop_4_rc0e15c_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem global_zero_ball_mass_bound_tf (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R : ℝ} (hR : 0<R) (c : FinProbability Y) (hc : c.coeff.support.card≤n+1)
    (r : ℝ) (hr : 0 ≤ r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r).toReal≤C*ε := by
  sorry

end

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end
