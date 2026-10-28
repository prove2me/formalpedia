-- Prove2me | Theorems.Thm_OAI_Coulomb_strictly_bound_sequence_tight
-- name    : OAI.Coulomb.strictly_bound_sequence_tight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:07:27.383784+00:00
-- url     : https://prove2.me/theorems/a99803ed-1ebb-46d6-b459-0efcfd791d79
-- title:
--   OAI.Coulomb.strictly_bound_sequence_tight: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Coulomb.strictly_bound_sequence_tight` of [lean/OAI/Analysis/CoulombRadii/SpectralTheory/StrictBinding.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/StrictBinding.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Coulomb`, with `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators Classical`):
--
--   ```lean
--   lemma strictly_bound_sequence_tight (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
--       (u:ℕ → H1Vector n) (ha:∀ k,Antisymmetric (u k)) (hm:∀ k,mass (u k)=1)
--       (E P:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n)
--       (hP:(P:EReal) ≤ sectorFormBottom (atom Z hZ) (n-1)) (hgap:E<P)
--       (hlim:Tendsto (fun k => form (atom Z hZ) (u k)) atTop (𝓝 E)) :
--       ∀ ε:ℝ,0<ε → ∃ A:Set (Configuration n),∃ hA:MeasurableSet A,volume A≠(⊤:ℝ≥0∞) ∧
--         ∀ᶠ k in atTop,∀ s,‖cutL2 Aᶜ hA.compl ((u k).valueL2 s)‖≤ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.Configuration`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Spins`, `OAI.Coulomb.form` and `OAI.Coulomb.mass` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.cutL2` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom`, `OAI.Coulomb.sectorFormBottom` and `OAI.Coulomb.H1Vector.valueL2` (definitions bundle `OAIQ062C004` of this split).
--
--   **Used by.** The proof of `OAI.Coulomb.atom_strict_binding_attained` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/StrictBinding.lean (declaration OAI.Coulomb.strictly_bound_sequence_tight)

import Mathlib
import Definitions.Def_OAIQ062C002
import Definitions.Def_OAIQ062C004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb

lemma strictly_bound_sequence_tight (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (u:ℕ → H1Vector n) (ha:∀ k,Antisymmetric (u k)) (hm:∀ k,mass (u k)=1)
    (E P:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n)
    (hP:(P:EReal) ≤ sectorFormBottom (atom Z hZ) (n-1)) (hgap:E<P)
    (hlim:Tendsto (fun k => form (atom Z hZ) (u k)) atTop (𝓝 E)) :
    ∀ ε:ℝ,0<ε → ∃ A:Set (Configuration n),∃ hA:MeasurableSet A,volume A≠(⊤:ℝ≥0∞) ∧
      ∀ᶠ k in atTop,∀ s,‖cutL2 Aᶜ hA.compl ((u k).valueL2 s)‖≤ε := by
  sorry

end Coulomb
end

end

end OAI
end
