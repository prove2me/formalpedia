-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direction_stable_closed_cell_bound
-- name    : OAI.RVM.Admissible.direction_stable_closed_cell_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:31.924172+00:00
-- url     : https://prove2.me/theorems/3cf9a253-f5a7-4fb9-a5e3-c0e749f904d9
-- title:
--   OAI.RVM.Admissible.direction_stable_closed_cell_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direction_stable_closed_cell_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direction_stable_closed_cell_bound {d₀ : Datum} (hd₀ : Admissible d₀)
--       (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
--       ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (B : ClosedConeBin) (a b c d e m δ φ : ℝ),
--         zX∈tsupport d₀.f₀ → 0 ≤ c → c≤d → d≤e → e≤T → Icc a b⊆Icc c e →
--         0 < m → m≤B.qmin → m≤B.wmin →
--         e-c≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
--         e-c≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
--         0<B.rmin → 0≤B.rmax → 0<φ →
--         B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → 4≤φ*B.wmin →
--         2*δ+2*((m/2)⁻¹)^2≤φ/16 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         ENNReal.ofReal (B.qmin/2)*labelOccupation (fun z=>s.f (0,z))
--           (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d)≤
--         ENNReal.ofReal (C*B.rmax*(Real.log (2+P))^6/δ)*ENNReal.ofReal (datumEnergyNumber d₀)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.closedBinHits`, `OAI.RVM.datumEnergyNumber` and `OAI.RVM.labelOccupation` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_closedEulerian_grid` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean (declaration OAI.RVM.Admissible.direction_stable_closed_cell_bound)

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
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direction_stable_closed_cell_bound {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b c d e m δ φ : ℝ),
      zX∈tsupport d₀.f₀ → 0 ≤ c → c≤d → d≤e → e≤T → Icc a b⊆Icc c e →
      0 < m → m≤B.qmin → m≤B.wmin →
      e-c≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      e-c≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      0<B.rmin → 0≤B.rmax → 0<φ →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → 4≤φ*B.wmin →
      2*δ+2*((m/2)⁻¹)^2≤φ/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ENNReal.ofReal (B.qmin/2)*labelOccupation (fun z=>s.f (0,z))
        (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d)≤
      ENNReal.ofReal (C*B.rmax*(Real.log (2+P))^6/δ)*ENNReal.ofReal (datumEnergyNumber d₀) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
