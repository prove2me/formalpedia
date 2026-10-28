-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_actual_transferred_limit
-- name    : OAI.ElasticityDistribution.actual_transferred_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:45:20.231248+00:00
-- url     : https://prove2.me/theorems/ca9a0112-ea56-456a-8f9d-4e42705b0e44
-- title:
--   OAI.ElasticityDistribution.actual_transferred_limit: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.actual_transferred_limit` of [lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open Set Filter MeasureTheory TemperedDistribution`, `open scoped SchwartzMap Topology BigOperators`, `open ElasticityAugmented`, `open ElasticityCGO (augEmbed)`, `open ElasticityBessel (L2)`, `open ElasticityPhysicalEstimate (physicalAug)`, `open ElasticityPhysicalAlgebra (phase physical)`):
--
--   ```lean
--   theorem actual_transferred_limit (B K : Set X) (α β : X)
--       (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
--       (lam m : Coeff) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0)
--       (u v : ℕ → Fin 3 → SchwartzMap X ℂ) (a : Fin 4 → SchwartzMap X ℂ)
--       (hv : ∀ n i,EqOn (physical (phase (h n) α β) (eval lam) (eval m) (v n) i : X → ℂ) 0 B)
--       (hs : ∀ n i,tsupport (v n i-u n i : SchwartzMap X ℂ)⊆K)
--       (C : ℝ) (hC : ∀ n,‖augEmbed (physicalAug (phase (h n) α β) (v n))‖≤C)
--       (ha : ∀ i,Tendsto (fun n => L2 (physicalAug (phase (h n) α β) (u n) i)) atTop (𝓝 (L2 (a i)))) :
--       ∃ W : AugHilbert,
--         (∀ i,LocalEq B (leadingRd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
--           (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
--         LocalEq B (leadingSd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
--           (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
--         LocalEq B (normald (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (fun j => (W j.succ : Dist))) 0 ∧
--         ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityCGO.S`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist`, `OAI.ElasticityDistribution.X` and `OAI.ElasticityDistribution.eval` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityBessel.L2`, `OAI.ElasticityCGO.augEmbed`, `OAI.ElasticityDistribution.AugHilbert`, `OAI.ElasticityDistribution.LocalEq`, `OAI.ElasticityPhysicalAlgebra.phase` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.normald` (definitions bundle `OAIQ6El005` of this split); `OAI.ElasticityDistribution.leadingRd`, `OAI.ElasticityDistribution.leadingSd` and `OAI.ElasticityPhysicalEstimate.physicalAug` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_weak_transport_column` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean (declaration OAI.ElasticityDistribution.actual_transferred_limit)

import Mathlib
import Definitions.Def_OAIQ6El006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution

open Set Filter MeasureTheory TemperedDistribution
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCGO (augEmbed)
open ElasticityBessel (L2)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityPhysicalAlgebra (phase physical)

theorem actual_transferred_limit (B K : Set X) (α β : X)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Coeff) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0)
    (u v : ℕ → Fin 3 → SchwartzMap X ℂ) (a : Fin 4 → SchwartzMap X ℂ)
    (hv : ∀ n i,EqOn (physical (phase (h n) α β) (eval lam) (eval m) (v n) i : X → ℂ) 0 B)
    (hs : ∀ n i,tsupport (v n i-u n i : SchwartzMap X ℂ)⊆K)
    (C : ℝ) (hC : ∀ n,‖augEmbed (physicalAug (phase (h n) α β) (v n))‖≤C)
    (ha : ∀ i,Tendsto (fun n => L2 (physicalAug (phase (h n) α β) (u n) i)) atTop (𝓝 (L2 (a i)))) :
    ∃ W : AugHilbert,
      (∀ i,LocalEq B (leadingRd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
        (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq B (leadingSd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
        (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq B (normald (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (fun j => (W j.succ : Dist))) 0 ∧
      ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist) := by
  sorry

end ElasticityDistribution

end

end OAI
end
