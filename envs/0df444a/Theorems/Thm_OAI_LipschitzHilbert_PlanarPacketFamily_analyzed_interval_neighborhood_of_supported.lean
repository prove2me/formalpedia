-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PlanarPacketFamily_analyzed_interval_neighborhood_of_supported
-- name    : OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:41:13.559327+00:00
-- url     : https://prove2.me/theorems/58c7797d-a52d-4c9a-8331-85552c6716df
-- title:
--   OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported` of [lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedAnalyzedNeighborhood.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedAnalyzedNeighborhood.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PlanarPacketFamily`, with `open MeasureTheory Set`, `open scoped FourierTransform ENNReal`):
--
--   ```lean
--   theorem analyzed_interval_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
--       (hlo : 0 < lo) (hhi : 0 ≤ hi) :
--       ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
--         [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
--         (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (_hv : Measurable v)
--         (g : ℝ × ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
--         (_hderiv : ∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
--           (lineEnvelope (P.centerX j u) (P.length j) 3 x *
--             lineEnvelope (P.centerZ j u) P.width 2 y)),
--         Monotone d →
--         (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
--         (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
--         ∀ (synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
--           (frequency : κ → ℝ) (C c r : ℝ), 0 < C → 0 < r →
--         (∀ i y j u k x, ‖synth i j u k y x‖ ≤ C*
--           (lineEnvelope (P.centerX j u) (P.length j) 3 x *
--             lineEnvelope (P.centerZ j u) P.width 2 y)) →
--         (∀ i y j u k x, ‖deriv (synth i j u k y) x‖ ≤ (C/P.length j)*
--           (lineEnvelope (P.centerX j u) (P.length j) 3 x *
--             lineEnvelope (P.centerZ j u) P.width 2 y)) →
--         (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (synth i j u k y) ξ = 0) →
--         (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (synth i j u k y) ξ = 0) →
--         (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
--           (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x) →
--         (∀ j u k, Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2)) →
--         (∀ j u k x t, DifferentiableAt ℝ (fun y => synth 0 j u k y x) t) →
--         (∀ j u k, Continuous (fun z : ℝ × ℝ =>
--           deriv (fun t => synth 0 j u k t z.2) z.1 -
--             (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2)) →
--         ∀ (grid : FiniteLineGrid), 1 < grid.branching → (∀ j (_u : ι j), P.length j ≤ grid.width) →
--         ∀ n : ℕ, 1 ≤ n →
--         let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) grid.branching
--         ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
--           (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
--           ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w,
--             x ∈ grid.root → |z-c| ≤ r → |w| ≤ r → (x,z) ∉ bad →
--             ‖planarPacketInterval (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
--               (fun j u k y x => synth 0 j u k y x) a b x (z+w)‖ ≤ 8*K*(n:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.FiniteLineGrid`, `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PlanarPacketFamily`, `OAI.LipschitzHilbert.lineEnvelope`, `OAI.LipschitzHilbert.planarPacketInterval`, `OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure`, `OAI.LipschitzHilbert.FiniteLineGrid.root`, `OAI.LipschitzHilbert.PlanarPacketFamily.centerX`, `OAI.LipschitzHilbert.PlanarPacketFamily.centerZ`, `OAI.LipschitzHilbert.PlanarPacketFamily.coefficientScale`, `OAI.LipschitzHilbert.PlanarPacketFamily.length` and `OAI.LipschitzHilbert.PlanarPacketFamily.mainCoefficient` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.lineMomentBase` (definitions bundle `OAIQ090A001` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedAnalyzedNeighborhood.lean (declaration OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert.PlanarPacketFamily

theorem analyzed_interval_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (_hderiv : ∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)),
      Monotone d →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (C c r : ℝ), 0 < C → 0 < r →
      (∀ i y j u k x, ‖synth i j u k y x‖ ≤ C*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k x, ‖deriv (synth i j u k y) x‖ ≤ (C/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => synth 0 j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => synth 0 j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching → (∀ j (_u : ι j), P.length j ≤ grid.width) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w,
          x ∈ grid.root → |z-c| ≤ r → |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
            (fun j u k y x => synth 0 j u k y x) a b x (z+w)‖ ≤ 8*K*(n:ℝ) := by
  sorry

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end
