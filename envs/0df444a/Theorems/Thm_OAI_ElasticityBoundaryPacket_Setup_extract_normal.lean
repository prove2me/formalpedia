-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_extract_normal
-- name    : OAI.ElasticityBoundaryPacket.Setup.extract_normal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:25:56.895827+00:00
-- url     : https://prove2.me/theorems/28bd6f94-4d4b-4c5d-a3a7-7fae8052fba1
-- title:
--   OAI.ElasticityBoundaryPacket.Setup.extract_normal: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPacket.Setup.extract_normal` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPacket`, with `open Set Filter MeasureTheory`, `open scoped Topology BigOperators`, `open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryMixedScaling`):
--
--   ```lean
--   lemma Setup.extract_normal (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
--       (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
--       (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
--       (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
--       (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
--       (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
--       (n : ℕ) (H : I → I → I → I → Y → ℂ)
--       (hHc : ∀ i α j β, Continuous (H i α j β))
--       (hHs : ∀ i α j β, HasCompactSupport (H i α j β))
--       (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K →
--         s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
--         s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^n*H i α j β y)
--       (p₀ q₀ : W) (hp₀ : normal (l₁ x) (m₁ x) p₀=0) (hq₀ : normal (l₂ x) (m₂ x) q₀=0) :
--       frozenPair n (fun i α j β => H i α j β 0) p₀ q₀=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMVNormal.normal`, `OAI.ElasticityBoundaryPacket.I`, `OAI.ElasticityBoundaryPacket.Setup`, `OAI.ElasticityBoundaryPacket.X`, `OAI.ElasticityBoundaryPacket.Y`, `OAI.ElasticityBoundaryPacket.frozenPair` and `OAI.ElasticityBoundaryPacket.Setup.rawCoeff` (definitions bundle `OAIQ6El001` of this split); `OAI.Elasticity.Admissible`, `OAI.Elasticity.BoundaryData` and `OAI.Elasticity.DN` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proofs of `OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step` and `OAI.ElasticityBoundaryPacket.boundary_values_global` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean (declaration OAI.ElasticityBoundaryPacket.Setup.extract_normal)

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryPacket

open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryMixedScaling
  ElasticityBoundaryLimit ElasticityBoundaryMVCalculus ElasticityBoundaryWeights
  ElasticityBoundaryTensorSeries ElasticityBoundaryParameter
variable {Ω : Set X} {x : X}

lemma Setup.extract_normal (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (n : ℕ) (H : I → I → I → I → Y → ℂ)
    (hHc : ∀ i α j β, Continuous (H i α j β))
    (hHs : ∀ i α j β, HasCompactSupport (H i α j β))
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K →
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^n*H i α j β y)
    (p₀ q₀ : W) (hp₀ : normal (l₁ x) (m₁ x) p₀=0) (hq₀ : normal (l₂ x) (m₂ x) q₀=0) :
    frozenPair n (fun i α j β => H i α j β 0) p₀ q₀=0 := by
  sorry

end ElasticityBoundaryPacket

end

end OAI
end
