-- Prove2me | Theorems.Thm_OAI_NeutralAtom_atomic_global_master_potential
-- name    : OAI.NeutralAtom.atomic_global_master_potential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:18:11.447899+00:00
-- url     : https://prove2.me/theorems/600c914d-8275-41d0-9d6b-07eb015a56dc
-- title:
--   OAI.NeutralAtom.atomic_global_master_potential: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.atomic_global_master_potential` of [lean/OAI/Analysis/CoulombRadii/FieldAnalysis/AtomicGlobalScale.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/FieldAnalysis/AtomicGlobalScale.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal BigOperators Classical SchwartzMap`):
--
--   ```lean
--   theorem atomic_global_master_potential : ∃ C : ℝ,0<C ∧
--       ∀ {N : ℕ} (Z : ℕ) (hZ : 1≤Z) (u : Coulomb.H1Vector (N+1)),Coulomb.Antisymmetric u →
--       Coulomb.mass u=1 → (N+1:ℝ)≤3*(Z:ℝ) → Coulomb.form (Coulomb.atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) →
--       ∀ (g : 𝓢(Position,ℝ)),(∫ w,g w^2)=1 →
--       (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
--       ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
--       ∀ y : Position,potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤C*(Z:ℝ)^(4/3:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.form` and `OAI.Coulomb.mass` (definitions bundle `OAIQ062C000` of this split); `OAI.NeutralAtom.potentialOf` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.mixturePacketDensity`, `OAI.NeutralAtom.packetExponent` and `OAI.NeutralAtom.rawLaw` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.fromH1Wave` (definitions bundle `OAIQ062C007` of this split); `OAI.NeutralAtom.Position` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proof of `OAI.NeutralAtom.physical_initial_event` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/FieldAnalysis/AtomicGlobalScale.lean (declaration OAI.NeutralAtom.atomic_global_master_potential)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section

namespace NeutralAtom

theorem atomic_global_master_potential : ∃ C : ℝ,0<C ∧
    ∀ {N : ℕ} (Z : ℕ) (hZ : 1≤Z) (u : Coulomb.H1Vector (N+1)),Coulomb.Antisymmetric u →
    Coulomb.mass u=1 → (N+1:ℝ)≤3*(Z:ℝ) → Coulomb.form (Coulomb.atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) →
    ∀ (g : 𝓢(Position,ℝ)),(∫ w,g w^2)=1 →
    (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
    ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    ∀ y : Position,potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤C*(Z:ℝ)^(4/3:ℝ) := by
  sorry
end NeutralAtom
end

end

end OAI
end
