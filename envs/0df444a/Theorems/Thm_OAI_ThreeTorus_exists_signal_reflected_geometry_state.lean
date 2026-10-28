-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exists_signal_reflected_geometry_state
-- name    : OAI.ThreeTorus.exists_signal_reflected_geometry_state
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:05:44.003872+00:00
-- url     : https://prove2.me/theorems/1598667c-a042-4c60-b92d-e32317024088
-- title:
--   OAI.ThreeTorus.exists_signal_reflected_geometry_state: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exists_signal_reflected_geometry_state` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/SymmetricPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/SymmetricPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open Set Function Filter MeasureTheory`, `open scoped Topology BigOperators`):
--
--   ```lean
--   theorem exists_signal_reflected_geometry_state
--       {b D : ℝ} (hb : 0 < b) (hbD : b < D)
--       {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
--       (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
--       (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
--       ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
--         ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
--         (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
--         ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
--         Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
--         (∀ i, b ≤ |(F.m i:ℝ)/B|) →
--         ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
--         ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
--           ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
--             Injective G.m ∧ G.SpareIndependent ∧
--             G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
--             (∀ i,
--               (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
--                 outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
--               (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
--                 (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
--             StateTracks F G Sigma.fst B (g.scale B n) η ∧
--           ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
--             (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧
--             ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ G.GoodArc δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.PassageGeometryFamily`, `OAI.ThreeTorus.PassageOutputIndex`, `OAI.ThreeTorus.PassagePackets`, `OAI.ThreeTorus.StateTracks`, `OAI.ThreeTorus.TripleTorus`, `OAI.ThreeTorus.outputDensity`, `OAI.ThreeTorus.outputVector`, `OAI.ThreeTorus.packet`, `OAI.ThreeTorus.passageChart`, `OAI.ThreeTorus.phaseHaar`, `OAI.ThreeTorus.signalCircleModel`, `OAI.ThreeTorus.signalPrimeProduct`, `OAI.ThreeTorus.tripleVolume`, `OAI.ThreeTorus.PassageGeometryFamily.scale`, `OAI.ThreeTorus.PassagePackets.GoodArc`, `OAI.ThreeTorus.PassagePackets.Reflection`, `OAI.ThreeTorus.PassagePackets.SpareIndependent` and `OAI.ThreeTorus.PassagePackets.density` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proof of `OAI.ThreeTorus.exists_concrete_colored_controlled_signal` of this split imports it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/SymmetricPackets.lean (declaration OAI.ThreeTorus.exists_signal_reflected_geometry_state)

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
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_reflected_geometry_state
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          StateTracks F G Sigma.fst B (g.scale B n) η ∧
        ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
          (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧
          ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ G.GoodArc δ := by
  sorry

end ThreeTorus
end
end

end OAI
end
