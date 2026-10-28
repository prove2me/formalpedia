-- Prove2me | Theorems.Thm_OAI_Elasticity_physical_classical_transfer
-- name    : OAI.Elasticity.physical_classical_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:34:20.146979+00:00
-- url     : https://prove2.me/theorems/984bd631-0a63-4b95-8062-f8842a5661c2
-- title:
--   OAI.Elasticity.physical_classical_transfer: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.physical_classical_transfer` of [lean/OAI/MathematicalPhysics/Elasticity/WeakSolutions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakSolutions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open MeasureTheory Set SchwartzMap TemperedDistribution`, `open scoped BigOperators SchwartzMap LineDeriv`, `open ElasticityDistribution`):
--
--   ```lean
--   theorem physical_classical_transfer
--       (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
--       (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hΩB : Ω⊆B)
--       (hB : IsOpen B) (hB' : IsOpen B') (hsub : B'⊆B)
--       (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
--       (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
--       (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
--       (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
--       (L₁ M₁ L₂ M₂ N₂ O₂ : Coeff) (hN : N₂*M₂=1) (hO : O₂*(L₂+M₂+M₂)=1)
--       (hL₁ : ∀ᵐ x ∂(volume.restrict B), eval L₁ x=(lam₁ x : ℂ))
--       (hM₁ : ∀ᵐ x ∂(volume.restrict B), eval M₁ x=(mu₁ x : ℂ))
--       (hL₂ : ∀ᵐ x ∂(volume.restrict B), eval L₂ x=(lam₂ x : ℂ))
--       (hM₂ : ∀ᵐ x ∂(volume.restrict B), eval M₂ x=(mu₂ x : ℂ))
--       {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
--       (hs : tsupport g⊆B) (h1 : Set.EqOn g 1 B') (F : Fin 3 → SchwartzMap X ℂ)
--       (hF : ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₁) (eval M₁) F i : X → ℂ) 0 B) :
--       ∃ G : Fin 3 → SchwartzMap X ℂ,
--         (∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) G i : X → ℂ) 0 B') ∧
--         ∀ i, Set.EqOn (G i : X → ℂ) (F i) (B'\closure Ω)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Elasticity.BoundedCoefficient`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.X` and `OAI.ElasticityDistribution.eval` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.Admissible`, `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proofs of `OAI.Elasticity.extended_dn_amplitude_transfer` and `OAI_Elasticity_physical_supported_transfer` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakSolutions.lean (declaration OAI.Elasticity.physical_classical_transfer)

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

section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω B B' : Set X} {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
theorem physical_classical_transfer
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hΩB : Ω⊆B)
    (hB : IsOpen B) (hB' : IsOpen B') (hsub : B'⊆B)
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    (L₁ M₁ L₂ M₂ N₂ O₂ : Coeff) (hN : N₂*M₂=1) (hO : O₂*(L₂+M₂+M₂)=1)
    (hL₁ : ∀ᵐ x ∂(volume.restrict B), eval L₁ x=(lam₁ x : ℂ))
    (hM₁ : ∀ᵐ x ∂(volume.restrict B), eval M₁ x=(mu₁ x : ℂ))
    (hL₂ : ∀ᵐ x ∂(volume.restrict B), eval L₂ x=(lam₂ x : ℂ))
    (hM₂ : ∀ᵐ x ∂(volume.restrict B), eval M₂ x=(mu₂ x : ℂ))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : Set.EqOn g 1 B') (F : Fin 3 → SchwartzMap X ℂ)
    (hF : ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₁) (eval M₁) F i : X → ℂ) 0 B) :
    ∃ G : Fin 3 → SchwartzMap X ℂ,
      (∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) G i : X → ℂ) 0 B') ∧
      ∀ i, Set.EqOn (G i : X → ℂ) (F i) (B'\closure Ω) := by
  sorry
end Elasticity

end
end

end OAI
end
