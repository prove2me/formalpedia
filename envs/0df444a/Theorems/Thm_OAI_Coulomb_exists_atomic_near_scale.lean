-- Prove2me | Theorems.Thm_OAI_Coulomb_exists_atomic_near_scale
-- name    : OAI.Coulomb.exists_atomic_near_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:20:26.637518+00:00
-- url     : https://prove2.me/theorems/29992855-e365-4075-a6d3-486228a12484
-- title:
--   OAI.Coulomb.exists_atomic_near_scale: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Coulomb.exists_atomic_near_scale` of [lean/OAI/Analysis/CoulombRadii/FieldAnalysis/AtomicNear.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/FieldAnalysis/AtomicNear.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Coulomb`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical Topology`):
--
--   ```lean
--   theorem exists_atomic_near_scale : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
--       ∀ {J n : ℕ} (S : Nuclei J), (∀ i,S.position i=0) →
--       ∀ (u : H1Vector n), Antisymmetric u → mass u=1 →
--       ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S u≤E+δ → 0≤δ →
--       ∀ (y : Space), y≠0 → atomicCellScale y < s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
--       ∀ {R : ℝ}, 0≤R → R≤4*atomicCellScale y →
--         potentialForm (nearPotential y R) u≤atomicNearConstant*(atomicCellScale y)^(-21/5:ℝ)*R^(1/5:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Nuclei`, `OAI.Coulomb.Space`, `OAI.Coulomb.atomicCellScale`, `OAI.Coulomb.form`, `OAI.Coulomb.mass` and `OAI.Coulomb.potentialForm` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.Coulomb.nearPotential` (definitions bundle `OAIQ062C007` of this split); `OAI.Coulomb.atomicNearConstant` (definitions bundle `OAIQ062C008` of this split).
--
--   **Used by.** The proof of `OAI.NeutralAtom.physical_retained_master_fresh_transfer` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/FieldAnalysis/AtomicNear.lean (declaration OAI.Coulomb.exists_atomic_near_scale)

import Mathlib
import Definitions.Def_OAIQ062C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem exists_atomic_near_scale : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i,S.position i=0) →
    ∀ (u : H1Vector n), Antisymmetric u → mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S u≤E+δ → 0≤δ →
    ∀ (y : Space), y≠0 → atomicCellScale y < s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∀ {R : ℝ}, 0≤R → R≤4*atomicCellScale y →
      potentialForm (nearPotential y R) u≤atomicNearConstant*(atomicCellScale y)^(-21/5:ℝ)*R^(1/5:ℝ) := by
  sorry
end Coulomb
end

end
end

end OAI
end
