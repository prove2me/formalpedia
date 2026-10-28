-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_force_bulk_receiver_residual_uniform
-- name    : OAI.RVM.Admissible.force_bulk_receiver_residual_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:54.852189+00:00
-- url     : https://prove2.me/theorems/4e0a76ee-d01b-4eb0-a6ba-e45515e45dc0
-- title:
--   OAI.RVM.Admissible.force_bulk_receiver_residual_uniform: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.force_bulk_receiver_residual_uniform` of [lean/OAI/Analysis/VlasovMaxwell/Population/BulkReceiverResidual.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BulkReceiverResidual.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.force_bulk_receiver_residual_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
--       ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
--         1≤P → 1≤Real.log (2+P) →
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (a b I w : ℝ),
--         zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
--         1≤w → w≤P → I≤(w/P)^2 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
--         (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--       ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
--         (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
--         (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
--         ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
--           (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
--             boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
--         ENNReal.ofReal ((4*Real.pi)⁻¹) *
--           (ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
--           ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.boundaryLorentzForce`, `OAI.RVM.datumBoundarySolution` and `OAI.RVM.prefixMomentumForce` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross`, `OAI.RVM.q` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.force_bulk_uniform` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BulkReceiverResidual.lean (declaration OAI.RVM.Admissible.force_bulk_receiver_residual_uniform)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.force_bulk_receiver_residual_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal ((4*Real.pi)⁻¹) *
        (ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
