-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exists_two_slow_insertions
-- name    : OAI.ThreeTorus.exists_two_slow_insertions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:06:05.11479+00:00
-- url     : https://prove2.me/theorems/8106e03d-e700-425f-ac7d-56ae40e701c0
-- title:
--   OAI.ThreeTorus.exists_two_slow_insertions: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exists_two_slow_insertions` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/TensorPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/TensorPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open Set Function Filter MeasureTheory`, `open scoped Topology BigOperators ComplexConjugate`):
--
--   ```lean
--   theorem exists_two_slow_insertions (F H : RealPacketFamily) (hmi : Injective F.data.m)
--       {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.data.GoodArc δ) (hgH : H.data.GoodArc δ) (hV : H.data.V=F.data.V)
--       (c : TensorIndex →₀ ℂ) (hc0 : c 0=0) (hcr : ∀ k, c (-k)=conj (c k))
--       (Q : PhysicalJetData) (frame : PhysicalFrame)
--       {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
--       ∃ F' H' : RealPacketFamily, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
--         Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
--         frame'.chart=frame.chart.trans α ∧ H'.data.V=F'.data.V ∧ Injective F'.data.m ∧
--         (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ F'.data.GoodArc δ' ∧ H'.data.GoodArc δ') ∧
--         Q.Close ζ frame F.data.V frame' F'.data.V ∧
--         physicalDist F.vector (F'.vector ∘ α) < ε ∧
--         physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x)
--           (H'.vector ∘ α) < ε ∧
--         (∫ z, |F'.density z-F.density z| ∂phaseHaar) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.PhysicalFrame`, `OAI.ThreeTorus.PhysicalJetData`, `OAI.ThreeTorus.RealPacketFamily`, `OAI.ThreeTorus.TensorIndex`, `OAI.ThreeTorus.TripleTorus`, `OAI.ThreeTorus.phaseHaar`, `OAI.ThreeTorus.physicalDist`, `OAI.ThreeTorus.tensorLast`, `OAI.ThreeTorus.tensorMiddle`, `OAI.ThreeTorus.tensorPolynomial`, `OAI.ThreeTorus.tripleVolume`, `OAI.ThreeTorus.PassagePackets.GoodArc`, `OAI.ThreeTorus.PassagePackets`, `OAI.ThreeTorus.PhysicalJetData.Close`, `OAI.ThreeTorus.RealPacketFamily.density` and `OAI.ThreeTorus.RealPacketFamily.vector` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proof of `OAI.ThreeTorus.StageState.exists_step` of this split imports it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/TensorPackets.lean (declaration OAI.ThreeTorus.exists_two_slow_insertions)

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
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

theorem exists_two_slow_insertions (F H : RealPacketFamily) (hmi : Injective F.data.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.data.GoodArc δ) (hgH : H.data.GoodArc δ) (hV : H.data.V=F.data.V)
    (c : TensorIndex →₀ ℂ) (hc0 : c 0=0) (hcr : ∀ k, c (-k)=conj (c k))
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ F' H' : RealPacketFamily, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ H'.data.V=F'.data.V ∧ Injective F'.data.m ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ F'.data.GoodArc δ' ∧ H'.data.GoodArc δ') ∧
      Q.Close ζ frame F.data.V frame' F'.data.V ∧
      physicalDist F.vector (F'.vector ∘ α) < ε ∧
      physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x)
        (H'.vector ∘ α) < ε ∧
      (∫ z, |F'.density z-F.density z| ∂phaseHaar) < ε := by
  sorry
end ThreeTorus
end
end

end OAI
end
