-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_eventually_selector_error_family_concentration_of_supported
-- name    : OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:50:39.795616+00:00
-- url     : https://prove2.me/theorems/db07325c-890d-46ee-ae7f-829899e76fb0
-- title:
--   OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported` of [lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedErrorFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedErrorFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLabeledLattice`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology BigOperators`):
--
--   ```lean
--   theorem eventually_selector_error_family_concentration_of_supported
--       (rate aWeight p M Lip : ℝ) (D K H J₀ : ℕ)
--       (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p)
--       (hM : 0 ≤ M) (hLip : 0 ≤ Lip) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
--         (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
--         (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
--         (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
--         (∀ top, (P top).absoluteConstant ≤ L^p) →
--         (∀ top, 6+2*(8*D+1) ≤ (P top).order) →
--       ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ top j l u k,
--           planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
--         (T : τ → SlopeBox),
--         (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^aWeight) D) →
--       ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
--         (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
--         wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
--         (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
--           (fun l => (T top).slope+(P top).rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
--       ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ),
--         (∀ top j l k, Measurable (b top j l k)) →
--         (∀ top j l k s, ‖b top j l k s‖ ≤ M) →
--         (∀ top j l k s, b top j l k s ≠ 0 →
--           |s-((T top).slope+(P top).rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
--         (∀ top j l k s, |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
--           ‖b top j l k s-b top j l k (T top).slope‖ ≤
--             Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
--         (∀ top j l k s, (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
--           b top j l k s = 0) →
--       ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
--       ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
--         (∀ top z, ‖g top z‖ ≤ 1) →
--         J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
--       ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
--         (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
--         ∀ top lower upper z shift, |shift| ≤ (T top).width → z ∉ bad →
--           let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
--             ((P top).physicalAngularErrorCoefficient (T top).slope (angle top) (b top) (v top) (g top))
--             0 lower upper x y
--           ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
--             ‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
--               (z.2-(T top).slope*z.1+shift)‖ ≤
--                 L^(2*p+7)*((T top).weight (L^aWeight) (D:ℝ) z)^8
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.SlopeBox.area`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.absoluteConstant`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalAngularErrorCoefficient`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawInterval`, `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.stepExponent` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.covariantSignal` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.SourceSupportedLabeledTopGeometry` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedErrorFamily.lean (declaration OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section

attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_selector_error_family_concentration_of_supported
    (rate aWeight p M Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p)
    (hM : 0 ≤ M) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
      (∀ top, 6+2*(8*D+1) ≤ (P top).order) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (T : τ → SlopeBox),
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^aWeight) D) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => (T top).slope+(P top).rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ),
      (∀ top j l k, Measurable (b top j l k)) →
      (∀ top j l k s, ‖b top j l k s‖ ≤ M) →
      (∀ top j l k s, b top j l k s ≠ 0 →
        |s-((T top).slope+(P top).rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b top j l k s-b top j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b top j l k s = 0) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
      ∀ top lower upper z shift, |shift| ≤ (T top).width → z ∉ bad →
        let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalAngularErrorCoefficient (T top).slope (angle top) (b top) (v top) (g top))
          0 lower upper x y
        ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
          ‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
            (z.2-(T top).slope*z.1+shift)‖ ≤
              L^(2*p+7)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  sorry

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end
