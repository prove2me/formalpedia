-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_PlanarLearning_full_source_cover_uniform
-- name    : OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:26:40.250543+00:00
-- url     : https://prove2.me/theorems/b4b5a8ef-11df-4700-9045-5b241f765156
-- title:
--   OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Planar/PlanarUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Planar/PlanarUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.PlanarLearning`, with `open Finset Real Filter SourceScales`, `open scoped Classical BigOperators Topology NNReal`):
--
--   ```lean
--   theorem full_source_cover_uniform {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
--       ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
--         [AddCommGroup V] [Module K V] [FiniteDimensional K V],∀ D R,Admissible σ η D R →
--       exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
--       ∀ (U : Finset (Projectivization K V)) (n : ℕ) (b τ : ℝ),
--       0<n → n≤U.card → 0≤b → b≤C*scaleKstar σ η D →
--       0<τ → τ≤C*σ^(-100*beta η) →
--       let P := scaleP σ η D R
--       ∃ caps : Finset (Finset (Projectivization K V)),
--         (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
--         (∀ S,Input U n b τ S → ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
--         log ((caps.card:ℝ)+1)≤200*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+P)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.SourceScales.Admissible`, `OAI.SharpLogRamsey.SourceScales.beta`, `OAI.SharpLogRamsey.SourceScales.scaleKstar` and `OAI.SharpLogRamsey.SourceScales.scaleP` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.PlanarLearning.Input` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.GeometricCover.uniform_four` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Planar/PlanarUniform.lean (declaration OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform)

import Mathlib
import Definitions.Def_OAIQ045S002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology NNReal
noncomputable section

theorem full_source_cover_uniform {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],∀ D R,Admissible σ η D R →
    exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V)) (n : ℕ) (b τ : ℝ),
    0<n → n≤U.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S,Input U n b τ S → ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤200*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+P) := by
  sorry

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end
