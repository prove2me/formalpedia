-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_SpatialPublic_actual_cover
-- name    : OAI.SharpLogRamsey.SpatialPublic.actual_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:26:38.97553+00:00
-- url     : https://prove2.me/theorems/7104ed63-f1f1-4d36-b191-7fbc792dc138
-- title:
--   OAI.SharpLogRamsey.SpatialPublic.actual_cover: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.SpatialPublic.actual_cover` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Spatial/SpatialActualCover.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Spatial/SpatialActualCover.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.SpatialPublic`, with `open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry DescriptionHeaders`, `open scoped Classical BigOperators Topology NNReal`):
--
--   ```lean
--   theorem actual_cover (δ C : ℝ) (hδ : 0 < δ) :
--       ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3 ≤ q → exp σ=(q:ℝ) →
--       ∀ (U : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
--         (n Jmax : ℕ) (P g b τ : ℝ) (L : ℝ≥0) (R p h M : ℕ),
--       0 < n → n ≤ U.card → σ^δ ≤ P → P ≤ σ/40 → g ≤ σ/2+C → 0 < p → (p:ℝ) ≤ σ^2 →
--       (n:ℝ)=exp (3*σ/2+g) → exp (σ/2-2*g/15) ≤ Jmax →
--       (∀ m,0 < m → m ≤ n → n ≤ 2*m → Budget σ P L R (Nat.log 2 m+2) p h) →
--       0 ≤ b → 0 < τ → τ ≤ 1/40 → 200*(q:ℝ)*P ≤ n →
--       b+log 2+4*P*τ ≤ P/1000000 →
--       50000*exp (-(95/100:ℝ)*(L:ℝ)) ≤ exp (-(b+log 2)-4*P*τ)/800 →
--       2*(q:ℝ)*P ≤ M →
--       let H := (Fintype.card (Projectivization (ZMod q) (Fin 4→ZMod q)):ℝ)*log 2
--       let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
--         log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q))):ℝ)+1)
--       ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
--         (∀ W ∈ caps,W⊆U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
--         (∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
--           (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
--           S⊆U → S.card=n → T.Nonempty → S.card ≤ T.card →
--           (q:ℝ)^4*exp (-b) ≤ (S.card:ℝ)*T.card →
--           (Incidence.incidenceCount S T:ℝ) ≤ τ*(S.card:ℝ)*T.card/q →
--           (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
--             (n:ℝ)/50 ≤ (S∩planePoints W).card) ∨
--           (∃ W ∈ caps,(n:ℝ)/4 ≤ (S∩W).card)) ∧
--         (caps.card:ℝ) ≤ (n+1:ℕ)*(Jmax+1:ℕ)*
--           (((Nat.card (Submodule (ZMod q) (Fin 4→ZMod q))*(n+1)+1:ℕ):ℝ)^Jmax)*exp E
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.Incidence.incidenceCount` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.PreparedProjectiveGeometry.planePoints`, `OAI.SharpLogRamsey.SpatialLearning.Budget`, `OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_3` and `OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_4` (definitions bundle `OAIQ045S001` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.GeometricCover.uniform_four` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Spatial/SpatialActualCover.lean (declaration OAI.SharpLogRamsey.SpatialPublic.actual_cover)

import Mathlib
import Definitions.Def_OAIQ045S000
import Definitions.Def_OAIQ045S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry DescriptionHeaders
open scoped Classical BigOperators Topology NNReal
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_3
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_4
theorem actual_cover (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3 ≤ q → exp σ=(q:ℝ) →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (n Jmax : ℕ) (P g b τ : ℝ) (L : ℝ≥0) (R p h M : ℕ),
    0 < n → n ≤ U.card → σ^δ ≤ P → P ≤ σ/40 → g ≤ σ/2+C → 0 < p → (p:ℝ) ≤ σ^2 →
    (n:ℝ)=exp (3*σ/2+g) → exp (σ/2-2*g/15) ≤ Jmax →
    (∀ m,0 < m → m ≤ n → n ≤ 2*m → Budget σ P L R (Nat.log 2 m+2) p h) →
    0 ≤ b → 0 < τ → τ ≤ 1/40 → 200*(q:ℝ)*P ≤ n →
    b+log 2+4*P*τ ≤ P/1000000 →
    50000*exp (-(95/100:ℝ)*(L:ℝ)) ≤ exp (-(b+log 2)-4*P*τ)/800 →
    2*(q:ℝ)*P ≤ M →
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4→ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q))):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
      (∀ W ∈ caps,W⊆U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
      (∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
        (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
        S⊆U → S.card=n → T.Nonempty → S.card ≤ T.card →
        (q:ℝ)^4*exp (-b) ≤ (S.card:ℝ)*T.card →
        (Incidence.incidenceCount S T:ℝ) ≤ τ*(S.card:ℝ)*T.card/q →
        (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
          (n:ℝ)/50 ≤ (S∩planePoints W).card) ∨
        (∃ W ∈ caps,(n:ℝ)/4 ≤ (S∩W).card)) ∧
      (caps.card:ℝ) ≤ (n+1:ℕ)*(Jmax+1:ℕ)*
        (((Nat.card (Submodule (ZMod q) (Fin 4→ZMod q))*(n+1)+1:ℕ):ℝ)^Jmax)*exp E := by
  sorry

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end
