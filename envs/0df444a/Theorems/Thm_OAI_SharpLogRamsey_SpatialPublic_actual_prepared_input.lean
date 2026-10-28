-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_SpatialPublic_actual_prepared_input
-- name    : OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:32:19.879549+00:00
-- url     : https://prove2.me/theorems/61d237b7-480d-415b-a892-79089cf38bbb
-- title:
--   OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Spatial/SpatialInputBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Spatial/SpatialInputBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.SpatialPublic`, with `open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry`, `open scoped Classical BigOperators Topology NNReal`):
--
--   ```lean
--   theorem actual_prepared_input (δ C : ℝ) (hδ : 0<δ) :
--       ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
--       ∀ (U S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
--         (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
--       S⊆U → S.Nonempty → T.Nonempty → S.card≤T.card →
--       ∀ (P g b τ : ℝ) (p : ℕ),0≤τ →
--       σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
--       (S.card:ℝ)=exp (3*σ/2+g) →
--       (q:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card →
--       (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/q →
--       (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
--         (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
--       (∃ (S' : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
--         (planes : List (Submodule (ZMod q) (Fin 4→ZMod q))),
--         S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
--         (planes.length:ℝ)≤exp (σ/2-2*g/15) ∧
--         (∀ W∈planes,Module.finrank (ZMod q) W=3) ∧
--         Input U S'.card planePoints (sized S' planePoints planes)
--           σ P g (b+log 2) (2*τ) (Real.toNNReal ((q:ℝ)/S'.card)) p S')
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.GreedyPreparation.sized` and `OAI.SharpLogRamsey.Incidence.incidenceCount` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.PreparedProjectiveGeometry.planePoints` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.SpatialPublic.Input` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.SpatialPublic.actual_cover` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Spatial/SpatialInputBridge.lean (declaration OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input)

import Mathlib
import Definitions.Def_OAIQ045S002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section

theorem actual_prepared_input (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (U S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
    S⊆U → S.Nonempty → T.Nonempty → S.card≤T.card →
    ∀ (P g b τ : ℝ) (p : ℕ),0≤τ →
    σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    (S.card:ℝ)=exp (3*σ/2+g) →
    (q:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card →
    (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/q →
    (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ (S' : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (planes : List (Submodule (ZMod q) (Fin 4→ZMod q))),
      S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (planes.length:ℝ)≤exp (σ/2-2*g/15) ∧
      (∀ W∈planes,Module.finrank (ZMod q) W=3) ∧
      Input U S'.card planePoints (sized S' planePoints planes)
        σ P g (b+log 2) (2*τ) (Real.toNNReal ((q:ℝ)/S'.card)) p S') := by
  sorry

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end
