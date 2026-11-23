-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realCharFunLimitOfAETendstoV1
-- name    : Kyprianou.Ch02.realCharFunLimitOfAETendstoV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:40:38.231588+00:00
-- url     : https://prove2.me/theorems/25798bd2-bd3c-43cf-b328-5a1c7bb1a982
-- title:
--   Real characteristic functions converge under almost-sure convergence
-- statement:
--   For measurable real random variables F_n→X P-almost surely, show characteristic functions converge pointwise. Rewrite charFun(P.map F_n) ξ using charFun_apply_real and integral_map; apply complex dominated convergence under the probability measure P to exp(i ξ F_n), bounded by 1. Transfer to finite-simple marked PRM approximations to close prmFiniteSimpleCharToRawKLSV1.
-- source:
--   Mathlib characteristic function and dominated convergence; Kyprianou (2006) Ch.2.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.realCharFunLimitOfAETendstoV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hF : ∀ n, Measurable (F n)) (hX : Measurable X)
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (𝓝 (X ω)))
    (ξ : ℝ) :
    Tendsto (fun n => charFun (P.map (F n)) ξ) atTop
      (𝓝 (charFun (P.map X) ξ)) := by sorry
