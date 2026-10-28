-- Prove2me | Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_actual_angular_family_bound
-- name    : OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:20:25.387247+00:00
-- url     : https://prove2.me/theorems/fe3e17f5-2794-438e-98c3-d4545c59997d
-- title:
--   OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff NNReal`):
--
--   ```lean
--   lemma SmoothClassicalPrefix.actual_angular_family_bound {d : Datum} {s : Solution} {T w : ℝ}
--       (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
--       (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
--       {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
--       (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
--       (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
--       (J : Set ℝ) (hJ : J⊆Icc 0 T) (hcell : ∀i∈S,Icc (a i) (b i)⊆J)
--       (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖) :
--       let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
--       (∑i∈S,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t
--         (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
--           boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖) ≤
--         ENNReal.ofReal (4*Real.pi)⁻¹ *
--          ((∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
--             (fun p=>ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
--               ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖) p) +
--           (∑i∈S,ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z))
--             Q (directionWeight (a i) (b i) (ℓ i)) G z‖) +
--           (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) +
--           (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
--             (selectedMultiplierBulkDensity s F.flow zX T Q G) p) +
--           ∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.actualLabelSignedForce`, `OAI.RVM.angularMultiplierCLM`, `OAI.RVM.boundaryLorentzForce`, `OAI.RVM.datumBoundarySolution`, `OAI.RVM.directionWeight`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.labelSelectedCutoff`, `OAI.RVM.selectedAngularMovingCost`, `OAI.RVM.selectedAngularWeightCost`, `OAI.RVM.selectedInitialKernel` and `OAI.RVM.selectedMultiplierBulkDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_physical_family_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean (declaration OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound)

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

lemma SmoothClassicalPrefix.actual_angular_family_bound {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hJ : J⊆Icc 0 T) (hcell : ∀i∈S,Icc (a i) (b i)⊆J)
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    (∑i∈S,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖) ≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       ((∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
          (fun p=>ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
            ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖) p) +
        (∑i∈S,ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z))
          Q (directionWeight (a i) (b i) (ℓ i)) G z‖) +
        (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) +
        (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
          (selectedMultiplierBulkDensity s F.flow zX T Q G) p) +
        ∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
