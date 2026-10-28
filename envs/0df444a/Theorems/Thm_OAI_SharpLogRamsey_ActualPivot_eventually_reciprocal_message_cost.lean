-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_ActualPivot_eventually_reciprocal_message_cost
-- name    : OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:22:36.654286+00:00
-- url     : https://prove2.me/theorems/ba4b305e-226e-40ea-ab6f-1a35d5b563d2
-- title:
--   OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/StepCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/StepCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.ActualPivot`, with `open Real Filter SourceScales`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem eventually_reciprocal_message_cost (i : ℕ) (η c C H : ℝ)
--       (hη : 0 < η) (hc : 0 < c) (hC : 0 < C) (hH : 0 ≤ H) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
--       ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
--         [Fintype (Projectivization (ZMod q) V)]
--         [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) V))]
--         [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Module.Dual (ZMod q) V)))],
--         Module.finrank (ZMod q) V=i+4 →
--       ∀ (D : ℝ) (R w n k m : ℕ), Admissible σ η D R →
--         1 ≤ w → c*(q:ℝ)*σ^(1+η) ≤ m →
--         (w:ℝ)*D ≤ C*σ^(1+η/2) → (w:ℝ) ≤ C*σ^(1+η/2) →
--         (4*(n+k):ℕ) ≤ C*(q:ℝ)*σ^(1+η/2) →
--         4 ≤ scaleP σ η D R → 16*scaleKstar σ η D+log 1000000 ≤ scaleP σ η D R →
--       reciprocalOutputCost (K:=ZMod q) (V:=V) (I:=Fin w)
--         (d:=i+1) (b:=16*scaleKstar σ η D) (P:=scaleP σ η D R) (H:=H)
--         w (Nat.log 2 w+1) (2*(n+k)) ≤ D*σ^(-η/3)*m
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.reciprocalOutputCost`, `OAI.SharpLogRamsey.SourceScales.Admissible`, `OAI.SharpLogRamsey.SourceScales.scaleKstar` and `OAI.SharpLogRamsey.SourceScales.scaleP` (definitions bundle `OAIQ045S000` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Marking.eventually_class_step` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/StepCost.lean (declaration OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost)

import Mathlib
import Definitions.Def_OAIQ045S000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter SourceScales
open scoped Classical Topology
noncomputable section

theorem eventually_reciprocal_message_cost (i : ℕ) (η c C H : ℝ)
    (hη : 0 < η) (hc : 0 < c) (hC : 0 < C) (hH : 0 ≤ H) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
      [Fintype (Projectivization (ZMod q) V)]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) V))]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Module.Dual (ZMod q) V)))],
      Module.finrank (ZMod q) V=i+4 →
    ∀ (D : ℝ) (R w n k m : ℕ), Admissible σ η D R →
      1 ≤ w → c*(q:ℝ)*σ^(1+η) ≤ m →
      (w:ℝ)*D ≤ C*σ^(1+η/2) → (w:ℝ) ≤ C*σ^(1+η/2) →
      (4*(n+k):ℕ) ≤ C*(q:ℝ)*σ^(1+η/2) →
      4 ≤ scaleP σ η D R → 16*scaleKstar σ η D+log 1000000 ≤ scaleP σ η D R →
    reciprocalOutputCost (K:=ZMod q) (V:=V) (I:=Fin w)
      (d:=i+1) (b:=16*scaleKstar σ η D) (P:=scaleP σ η D R) (H:=H)
      w (Nat.log 2 w+1) (2*(n+k)) ≤ D*σ^(-η/3)*m := by
  sorry
end
end SharpLogRamsey.ActualPivot

end

end OAI
end
