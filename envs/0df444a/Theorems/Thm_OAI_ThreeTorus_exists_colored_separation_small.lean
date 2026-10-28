-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exists_colored_separation_small
-- name    : OAI.ThreeTorus.exists_colored_separation_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:04:37.437753+00:00
-- url     : https://prove2.me/theorems/5723fb19-bf0c-4e89-a922-ecfee0a3c102
-- title:
--   OAI.ThreeTorus.exists_colored_separation_small: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exists_colored_separation_small` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/CyclicPrediction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/CyclicPrediction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open Set Function MeasureTheory`, `open scoped Topology BigOperators ComplexConjugate`):
--
--   ```lean
--   theorem exists_colored_separation_small {n : ℕ} (F : PassagePackets (Fin n))
--       (hd : ∀ i j, i ≠ j → F.m i = F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j))
--       (τ : Fin n → Fin n) (hτ : Involutive τ) (hr : F.Reflection τ)
--       (b : Fin n → ℂ) (Q : PhysicalJetData) (frame : PhysicalFrame)
--       {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
--       ∃ C : ColoredState (Fin n), ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
--         Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
--         frame'.chart=frame.chart.trans α ∧ C.Reflection τ ∧
--         (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ C.packets.GoodArc δ) ∧
--         Q.Close ζ frame F.V frame' C.packets.V ∧
--         physicalDist (finitePacketVector F.m F.A) (C.totalVector ∘ α) < ε ∧
--         physicalDist (fun x => ∑ i, b i*packet (F.m i) (F.A i) x)
--           ((fun x => ∑ i, b i*C.vector i x) ∘ α) < ε ∧
--         (∫ z, |blockTotal C.density z-(∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.ColoredState`, `OAI.ThreeTorus.PassagePackets`, `OAI.ThreeTorus.PhysicalFrame`, `OAI.ThreeTorus.PhysicalJetData`, `OAI.ThreeTorus.TripleTorus`, `OAI.ThreeTorus.blockTotal`, `OAI.ThreeTorus.finitePacketVector`, `OAI.ThreeTorus.packet`, `OAI.ThreeTorus.phaseHaar`, `OAI.ThreeTorus.physicalDist`, `OAI.ThreeTorus.tripleVolume`, `OAI.ThreeTorus.ColoredState.Reflection`, `OAI.ThreeTorus.ColoredState.density`, `OAI.ThreeTorus.ColoredState.totalVector`, `OAI.ThreeTorus.ColoredState.vector`, `OAI.ThreeTorus.PassagePackets.GoodArc`, `OAI.ThreeTorus.PassagePackets.Reflection`, `OAI.ThreeTorus.PassagePackets.cylinderCore`, `OAI.ThreeTorus.PassagePackets.marginalDensity` and `OAI.ThreeTorus.PhysicalJetData.Close` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proof of `OAI.ThreeTorus.StageState.exists_step` of this split imports it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/CyclicPrediction.lean (declaration OAI.ThreeTorus.exists_colored_separation_small)

import Mathlib
import Definitions.Def_OAIQ13Tt000

section

attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

theorem exists_colored_separation_small {n : ℕ} (F : PassagePackets (Fin n))
    (hd : ∀ i j, i ≠ j → F.m i = F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j))
    (τ : Fin n → Fin n) (hτ : Involutive τ) (hr : F.Reflection τ)
    (b : Fin n → ℂ) (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ C : ColoredState (Fin n), ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ C.Reflection τ ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ C.packets.GoodArc δ) ∧
      Q.Close ζ frame F.V frame' C.packets.V ∧
      physicalDist (finitePacketVector F.m F.A) (C.totalVector ∘ α) < ε ∧
      physicalDist (fun x => ∑ i, b i*packet (F.m i) (F.A i) x)
        ((fun x => ∑ i, b i*C.vector i x) ∘ α) < ε ∧
      (∫ z, |blockTotal C.density z-(∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε := by
  sorry
end ThreeTorus
end
end

end OAI
end
