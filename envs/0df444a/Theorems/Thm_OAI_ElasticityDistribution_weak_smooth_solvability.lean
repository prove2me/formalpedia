-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_weak_smooth_solvability
-- name    : OAI.ElasticityDistribution.weak_smooth_solvability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:47:16.852902+00:00
-- url     : https://prove2.me/theorems/11c3305c-982a-4187-9ec2-11cd91e464f2
-- title:
--   OAI.ElasticityDistribution.weak_smooth_solvability: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.weak_smooth_solvability` of [lean/OAI/MathematicalPhysics/Elasticity/Solvability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Solvability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open MeasureTheory Complex SchwartzMap`, `open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal`, `open MeasureTheory Complex SchwartzMap`, `open scoped BigOperators SchwartzMap LineDeriv`, `open scoped SchwartzMap LineDeriv BigOperators`, `open MeasureTheory Complex SchwartzMap`, `open scoped BigOperators SchwartzMap LineDeriv`, `open scoped BigOperators`, `open MeasureTheory Complex SchwartzMap`, `open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal`, `open MeasureTheory TemperedDistribution`, `open scoped ENNReal SchwartzMap BigOperators`, `open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds`, `open ElasticityPhysicalAlgebra (phase)`, `open ElasticityPhysicalDual`):
--
--   ```lean
--   theorem weak_smooth_solvability (R : ℝ) (hR : 1 ≤ R)
--       (Ω : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (α β : X) (hα : α ≠ 0)
--       (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
--       (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
--       (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
--       (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
--       (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
--       ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
--         ∀ f : Fin 3 → S, ∃ w : _root_.OAI.ElasticityPhysicalDual.H, ‖w‖ ≤ C*‖embed f‖ ∧
--           (∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
--             (fun j => (w j : Dist)) i) (f i : Dist)) ∧
--           ∀ i : Fin 4, ∀ g : X → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
--             ∃ v : BoundedContinuousFunction X ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : X → ℂ) ∧
--               smulLeftCLM ℂ g ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
--                 (fun j => (w j : Dist)) : Fin 4 → Dist) i) =
--                 ((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure X)) : Dist)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityDistribution.Dist`, `OAI.ElasticityDistribution.S`, `OAI.ElasticityDistribution.X`, `OAI.ElasticityPhysicalDual.H` and `OAI.ElasticityPhysicalDual.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityCoeffBounds.ExteriorConstant`, `OAI.ElasticityDistribution.LocalEq`, `OAI.ElasticityDistribution.divd`, `OAI.ElasticityDistribution.exteriorCoeff`, `OAI.ElasticityDistribution.phys` and `OAI.ElasticityPhysicalAlgebra.phase` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityPhysicalDual.embed` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityDistribution.physical_quantitative_correction` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Solvability.lean (declaration OAI.ElasticityDistribution.weak_smooth_solvability)

import Mathlib
import Definitions.Def_OAIQ6El006

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

theorem weak_smooth_solvability (R : ℝ) (hR : 1 ≤ R)
    (Ω : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ f : Fin 3 → S, ∃ w : _root_.OAI.ElasticityPhysicalDual.H, ‖w‖ ≤ C*‖embed f‖ ∧
        (∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
          (fun j => (w j : Dist)) i) (f i : Dist)) ∧
        ∀ i : Fin 4, ∀ g : X → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
          ∃ v : BoundedContinuousFunction X ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : X → ℂ) ∧
            smulLeftCLM ℂ g ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
              (fun j => (w j : Dist)) : Fin 4 → Dist) i) =
              ((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure X)) : Dist) := by
  sorry
end ElasticityDistribution

end

end OAI
end
