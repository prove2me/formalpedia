-- Prove2me | Theorems.Thm_OAI_ElasticityAugmented_exists_real_physical_series
-- name    : OAI.ElasticityAugmented.exists_real_physical_series
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:34:18.421987+00:00
-- url     : https://prove2.me/theorems/56b6cf57-9831-4c76-930a-7f60eabfbdcf
-- title:
--   OAI.ElasticityAugmented.exists_real_physical_series: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityAugmented.exists_real_physical_series` of [lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityAugmented`, with `open Set`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_real_physical_series {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
--       (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
--       (lam m : X → ℝ) (hl : ContDiff ℝ (⊤ : ℕ∞) lam) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
--       (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) :
--       let l := smoothOfReal lam hl
--       let μ := smoothOfReal m hm
--       let r := positiveRoot m hm (fun x => (hp x).1)
--       let hr := positiveRoot_nonzero m hm (fun x => (hp x).1)
--       ∃ a : Fin 3 → ℕ → Amplitude Smooth,
--       ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
--         (∀ ν,normal θ (a ν 0).1=0) ∧
--         (∀ ν,leadingR (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
--             (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0 ∧
--           leadingS (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
--             (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0) ∧
--         (∀ ν j,RecursOn hU θ l μ (a ν j) (a ν (j+1))) ∧
--         ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
--           ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
--             (changeS (l+μ) r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.LocalSmooth`, `OAI.ElasticityAugmented.RecursOn`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.changeP`, `OAI.ElasticityAugmented.changeS`, `OAI.ElasticityAugmented.leadingR`, `OAI.ElasticityAugmented.leadingS`, `OAI.ElasticityAugmented.localAmp`, `OAI.ElasticityAugmented.localCoord`, `OAI.ElasticityAugmented.normal` and `OAI.ElasticityAugmented.restrictSmooth` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityFrame.Amp`, `OAI.ElasticityFrame.Fiber` and `OAI.ElasticityFrame.fiber` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityAugmented.positiveRoot`, `OAI.ElasticityAugmented.positiveRoot_nonzero` and `OAI.ElasticityAugmented.smoothOfReal` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proofs of `OAI_Elasticity_dn_common_leading_frame` and `OAI.Elasticity.dn_common_normal_frame` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean (declaration OAI.ElasticityAugmented.exists_real_physical_series)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented

open Set
open scoped BigOperators

theorem exists_real_physical_series {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m : X → ℝ) (hl : ContDiff ℝ (⊤ : ℕ∞) lam) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) :
    let l := smoothOfReal lam hl
    let μ := smoothOfReal m hm
    let r := positiveRoot m hm (fun x => (hp x).1)
    let hr := positiveRoot_nonzero m hm (fun x => (hp x).1)
    ∃ a : Fin 3 → ℕ → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν 0).1=0) ∧
      (∀ ν,leadingR (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0 ∧
        leadingS (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0) ∧
      (∀ ν j,RecursOn hU θ l μ (a ν j) (a ν (j+1))) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
          (changeS (l+μ) r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x) := by
  sorry
end ElasticityAugmented

end

end OAI
end
