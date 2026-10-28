-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_packet
-- name    : OAI.ElasticityBoundaryPacket.Setup.packet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:35:21.452823+00:00
-- url     : https://prove2.me/theorems/66f17949-f51c-44b2-91da-f1d3b4f98676
-- title:
--   OAI.ElasticityBoundaryPacket.Setup.packet: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPacket.Setup.packet` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPacket`, with `open Set MeasureTheory`, `open scoped BigOperators`, `open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryActualTower`):
--
--   ```lean
--   lemma Setup.packet (s : Setup Ω x) {l m : X → ℝ}
--       (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
--       (ha : Admissible Ω l m) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
--       (hx : x∈closure Ω) (p₀ : W) (h₀ : normal (l x) (m x) p₀=0) (N : ℕ) :
--       ∃ q : Polynomial W, q.coeff 0=p₀ ∧ ∃ A B : ℝ, 0≤A ∧ 0≤B ∧
--         ∀ δ : ℝ, 0<δ → δ≤1 → complexTrialSize (s.trial q δ)≤A ∧
--         complexResidualSize (ha.1.boundedCoefficient hO hB)
--           (ha.2.1.boundedCoefficient hO hB) (s.trial q δ)≤B*δ^N
--   ```
--
--   **Definitions.** The statement is written with `OAI.Elasticity.complexResidualSize`, `OAI.Elasticity.complexTrialSize` and `OAI.Elasticity.SmoothUpTo.boundedCoefficient` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMVNormal.normal`, `OAI.ElasticityBoundaryPacket.I`, `OAI.ElasticityBoundaryPacket.Setup` and `OAI.ElasticityBoundaryPacket.X` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityBoundaryPacket.Setup.trial` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.Admissible`, `OAI.Elasticity.SmoothUpTo` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPacket.Setup.extract_normal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryData.lean (declaration OAI.ElasticityBoundaryPacket.Setup.packet)

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryPacket

section

open Set MeasureTheory
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma Setup.packet (s : Setup Ω x) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (ha : Admissible Ω l m) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hx : x∈closure Ω) (p₀ : W) (h₀ : normal (l x) (m x) p₀=0) (N : ℕ) :
    ∃ q : Polynomial W, q.coeff 0=p₀ ∧ ∃ A B : ℝ, 0≤A ∧ 0≤B ∧
      ∀ δ : ℝ, 0<δ → δ≤1 → complexTrialSize (s.trial q δ)≤A ∧
      complexResidualSize (ha.1.boundedCoefficient hO hB)
        (ha.2.1.boundedCoefficient hO hB) (s.trial q δ)≤B*δ^N := by
  sorry

end

open Set
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal

end ElasticityBoundaryPacket

end

end OAI
end
