-- Prove2me | Theorems.Thm_OAI_CoulombAtom_actual_expandedAnnulus_inverse_uniform_eventually
-- name    : OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:30:01.255458+00:00
-- url     : https://prove2.me/theorems/f7554980-abe6-466d-9d8c-e720d4479625
-- title:
--   OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/ExpandedAnnulusInverse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/ExpandedAnnulusInverse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter Set`, `open scoped Topology BigOperators`, `open CoulombAnalysis CoulombObservation CoulombBarrier`):
--
--   ```lean
--   theorem actual_expandedAnnulus_inverse_uniform_eventually {ι : Type*} {l : Filter ι}
--       {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
--       {F : ∀ i, fermionGraph (N i)} {B c₁ h xi δ : ℝ}
--       (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
--       (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
--       (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
--       (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
--         TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
--       ∀ᶠ i in l, ∀ (j : Fin (K i)) (y : Space),
--         (2:ℝ)^j.val*r₀ i ≤ s i →
--         ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ → ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i) →
--         OriginalPointInverseBounds (F i) (Z i) (lam i) (r₀ i) (s i) c₁ h xi j y
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombBarrier.tailPolynomialThreshold` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.OriginalPointInverseBounds` and `OAI.CoulombAtom.TailTiltState` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.Spins` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI_CoulombAtom_exists_actual_fullAnnulus_good_constant` and `OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/ExpandedAnnulusInverse.lean (declaration OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set
open scoped Topology BigOperators
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem actual_expandedAnnulus_inverse_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i →
      ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ → ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i) →
      OriginalPointInverseBounds (F i) (Z i) (lam i) (r₀ i) (s i) c₁ h xi j y := by
  sorry

end CoulombAtom

end

end OAI
end
