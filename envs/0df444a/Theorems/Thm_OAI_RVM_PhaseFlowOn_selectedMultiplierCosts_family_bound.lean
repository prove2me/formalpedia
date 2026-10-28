-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedMultiplierCosts_family_bound
-- name    : OAI.RVM.PhaseFlowOn.selectedMultiplierCosts_family_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:33.432268+00:00
-- url     : https://prove2.me/theorems/f298cf5e-c2c6-4277-9215-91791c0cfc99
-- title:
--   OAI.RVM.PhaseFlowOn.selectedMultiplierCosts_family_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.selectedMultiplierCosts_family_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff NNReal`):
--
--   ```lean
--   lemma PhaseFlowOn.selectedMultiplierCosts_family_bound {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
--       (Q : Set (Fin 4→ℕ)) {W W' : ℝ→Vec→L[ℝ]Vec}
--       (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p)))
--       {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
--       (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
--       (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
--       (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J) :
--       (∑i∈S,ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q
--         (directionWeight (a i) (b i) (ℓ i)) W W' p‖) ≤
--         (∑i∈S,∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q
--           (directionWeight (a i) (b i) (ℓ i)) W p) +
--         (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
--           (selectedMultiplierBulkDensity s F.flow zX T Q W) p) +
--         ∑i∈S,∫⁻p,selectedMultiplierMovingDensity s F.flow zX T Q
--           (directionWeight (a i) (b i) (ℓ i)) W' p
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.directionWeight`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.selectedMultiplierBulkDensity`, `OAI.RVM.selectedMultiplierCosts`, `OAI.RVM.selectedMultiplierMovingDensity` and `OAI.RVM.selectedMultiplierWeightDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean (declaration OAI.RVM.PhaseFlowOn.selectedMultiplierCosts_family_bound)

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
open scoped ENNReal Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.selectedMultiplierCosts_family_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p)))
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J) :
    (∑i∈S,ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q
      (directionWeight (a i) (b i) (ℓ i)) W W' p‖) ≤
      (∑i∈S,∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q
        (directionWeight (a i) (b i) (ℓ i)) W p) +
      (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
        (selectedMultiplierBulkDensity s F.flow zX T Q W) p) +
      ∑i∈S,∫⁻p,selectedMultiplierMovingDensity s F.flow zX T Q
        (directionWeight (a i) (b i) (ℓ i)) W' p := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
