-- Prove2me | Theorems.Thm_OAI_CoulombBarrier_selected_data_profile_subsequence
-- name    : OAI.CoulombBarrier.selected_data_profile_subsequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:38:36.227234+00:00
-- url     : https://prove2.me/theorems/68a7135f-f729-49fd-afe5-895b41824a53
-- title:
--   OAI.CoulombBarrier.selected_data_profile_subsequence: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombBarrier.selected_data_profile_subsequence` of [lean/OAI/Analysis/CoulombIonization/Ionization/SelectedProfileSubsequence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/SelectedProfileSubsequence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombBarrier`, with `open MeasureTheory Filter Set Metric`, `open scoped Topology`, `open CoulombAtom CoulombAnalysis`):
--
--   ```lean
--   lemma selected_data_profile_subsequence {Z s l τ : ℕ → ℝ} {N : ℕ → ℕ} {B C R Q : ℝ}
--       (d : ∀ n, SelectedQuantumData (Z n) (N n) (s n) (l n) (τ n) B C R)
--       (hZ : ∀ n, 0 ≤ Z n) (hs : ∀ n, 0 < s n) (hl : ∀ n, 1 ≤ l n)
--       (hs0 : Tendsto s atTop (𝓝 0)) (hl0 : Tendsto l atTop atTop)
--       (hτ0 : Tendsto τ atTop (𝓝 0)) (hB : 0 < B) (hC : 0 ≤ C) (hR : 0 < R)
--       (hQ : 0 ≤ Q) (hq : ∀ n, |(s n)^3*(Z n-(N n:ℝ))| ≤ Q) :
--       ∃ φ : ℕ → ℕ, StrictMono φ ∧
--         Tendsto (fun n => (s (φ n))^3*(Z (φ n)-(N (φ n):ℝ))) atTop (𝓝 tfResidualCharge)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.tfResidualCharge` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombBarrier.SelectedQuantumData` (definitions bundle `OAIQ071C010` of this split).
--
--   **Used by.** The proof of `OAI.CoulombAtom.generalized_ionization` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/SelectedProfileSubsequence.lean (declaration OAI.CoulombBarrier.selected_data_profile_subsequence)

import Mathlib
import Definitions.Def_OAIQ071C010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma selected_data_profile_subsequence {Z s l τ : ℕ → ℝ} {N : ℕ → ℕ} {B C R Q : ℝ}
    (d : ∀ n, SelectedQuantumData (Z n) (N n) (s n) (l n) (τ n) B C R)
    (hZ : ∀ n, 0 ≤ Z n) (hs : ∀ n, 0 < s n) (hl : ∀ n, 1 ≤ l n)
    (hs0 : Tendsto s atTop (𝓝 0)) (hl0 : Tendsto l atTop atTop)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hB : 0 < B) (hC : 0 ≤ C) (hR : 0 < R)
    (hQ : 0 ≤ Q) (hq : ∀ n, |(s n)^3*(Z n-(N n:ℝ))| ≤ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (s (φ n))^3*(Z (φ n)-(N (φ n):ℝ))) atTop (𝓝 tfResidualCharge) := by
  sorry

end CoulombBarrier

end

end OAI
end
