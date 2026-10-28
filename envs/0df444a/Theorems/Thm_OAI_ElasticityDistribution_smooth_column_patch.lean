-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_smooth_column_patch
-- name    : OAI.ElasticityDistribution.smooth_column_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:46:07.515071+00:00
-- url     : https://prove2.me/theorems/e1a4618a-8301-49a0-9d35-ad5d1ffd0bcc
-- title:
--   OAI.ElasticityDistribution.smooth_column_patch: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.smooth_column_patch` of [lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open Set Filter TemperedDistribution`, `open scoped SchwartzMap LineDeriv BigOperators Topology`, `open ElasticityAugmented`, `open ElasticityPhysicalAlgebra (toSmooth)`):
--
--   ```lean
--   theorem smooth_column_patch {K B : Set X} (hB : IsOpen B) (hKB : K⊆B)
--       (θ : Fin 3 → ℂ) (lam m : Coeff) (v φ : Fin 4 → Test) (a₀ : Fin 4 → Smooth)
--       (hs : ∀ i,tsupport (v i-φ i : Test)⊆K)
--       (hφ : ∀ i,EqOn (φ i : X → ℂ) (a₀ i : X → ℂ) B)
--       (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist) i) 0)
--       (he : LocalEq B (leadingSd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist)) 0)
--       (hn : LocalEq B (normald θ (fun j => (v j.succ : Dist))) 0)
--       (hn₀ : normal θ (fun j => a₀ j.succ)=0) :
--       ∃ a : Fin 4 → Smooth,
--         (∀ i,tsupport ((a i-a₀ i : Smooth) : X → ℂ)⊆K) ∧
--         (∀ i,EqOn (leadingR (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) i : X → ℂ) 0 B) ∧
--         EqOn (leadingS (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) : X → ℂ) 0 B ∧
--         normal θ (fun j => a j.succ)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.leadingR`, `OAI.ElasticityAugmented.leadingS`, `OAI.ElasticityAugmented.normal`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityDistribution.LocalEq` and `OAI.ElasticityDistribution.Test` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.normald` (definitions bundle `OAIQ6El005` of this split); `OAI.ElasticityDistribution.leadingRd` and `OAI.ElasticityDistribution.leadingSd` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proofs of `OAI_Elasticity_dn_common_leading_frame` and `OAI.Elasticity.dn_smooth_transport_column` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean (declaration OAI.ElasticityDistribution.smooth_column_patch)

import Mathlib
import Definitions.Def_OAIQ6El006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology
namespace ElasticityDistribution
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth)
theorem smooth_column_patch {K B : Set X} (hB : IsOpen B) (hKB : K⊆B)
    (θ : Fin 3 → ℂ) (lam m : Coeff) (v φ : Fin 4 → Test) (a₀ : Fin 4 → Smooth)
    (hs : ∀ i,tsupport (v i-φ i : Test)⊆K)
    (hφ : ∀ i,EqOn (φ i : X → ℂ) (a₀ i : X → ℂ) B)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist) i) 0)
    (he : LocalEq B (leadingSd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist)) 0)
    (hn : LocalEq B (normald θ (fun j => (v j.succ : Dist))) 0)
    (hn₀ : normal θ (fun j => a₀ j.succ)=0) :
    ∃ a : Fin 4 → Smooth,
      (∀ i,tsupport ((a i-a₀ i : Smooth) : X → ℂ)⊆K) ∧
      (∀ i,EqOn (leadingR (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) i : X → ℂ) 0 B) ∧
      EqOn (leadingS (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) : X → ℂ) 0 B ∧
      normal θ (fun j => a j.succ)=0 := by
  sorry
end ElasticityDistribution

end

end OAI
end
