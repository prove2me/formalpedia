-- Prove2me | Theorems.Thm_OAI_RadiusLens_lens_at_radius
-- name    : OAI.RadiusLens.lens_at_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:45:42.073712+00:00
-- url     : https://prove2.me/theorems/f4e5804e-fce6-4d2c-a164-adcbb26aacb3
-- title:
--   OAI.RadiusLens.lens_at_radius: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadiusLens.lens_at_radius` of [lean/OAI/Geometry/TranslativeCovering/RadiusLens.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/RadiusLens.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadiusLens`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set MeasureTheory CapCost SphericalLaw CapGeometry BlockGeometry`, `open scoped BigOperators`):
--
--   ```lean
--   lemma lens_at_radius {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I] [DecidableEq I]
--       (e : Sphere n) (axes : I → Sphere n) (τ : I → ℝ) (d : I → I → ℝ)
--       {l u u₀ t : ℝ} (hl : 0 < l) (hu : u < 1) (_hu₀ : 0 ≤ u₀)
--       (ht : 0 ≤ t) (ht1 : t < 1) (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u₀)
--       (hmetric : ∀ i j,(n:ℝ)*(ProjectiveCaps.angle (axes i).val (axes j).val)^2 ≤ d i j^2)
--       (S : Finset I) (hS : S.Nonempty) (a : I) (ha : a ∈ S)
--       (hmin : ∀ i ∈ S,(intensity e t).real (cap (axes a).val (τ a)) ≤
--         (intensity e t).real (cap (axes i).val (τ i)))
--       (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
--       (hrsmall : radius d S/(n:ℝ) < 2)
--       (hsmall : (u₀+radius d S/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2+
--         4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) ≤ u^2) (hu0 : 0 ≤ u) :
--       Real.exp (-(3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l)*
--         (1+radius d S+Real.log S.card))*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) ≤
--         (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BlockGeometry.radius`, `OAI.CapCost.intensity`, `OAI.ProjectiveCaps.angle`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.cap` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.WitnessConstruction.shell` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/RadiusLens.lean (declaration OAI.RadiusLens.lens_at_radius)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace RadiusLens
open Set MeasureTheory CapCost SphericalLaw CapGeometry BlockGeometry
open scoped BigOperators

lemma lens_at_radius {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I] [DecidableEq I]
    (e : Sphere n) (axes : I → Sphere n) (τ : I → ℝ) (d : I → I → ℝ)
    {l u u₀ t : ℝ} (hl : 0 < l) (hu : u < 1) (_hu₀ : 0 ≤ u₀)
    (ht : 0 ≤ t) (ht1 : t < 1) (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u₀)
    (hmetric : ∀ i j,(n:ℝ)*(ProjectiveCaps.angle (axes i).val (axes j).val)^2 ≤ d i j^2)
    (S : Finset I) (hS : S.Nonempty) (a : I) (ha : a ∈ S)
    (hmin : ∀ i ∈ S,(intensity e t).real (cap (axes a).val (τ a)) ≤
      (intensity e t).real (cap (axes i).val (τ i)))
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hrsmall : radius d S/(n:ℝ) < 2)
    (hsmall : (u₀+radius d S/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2+
      4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) ≤ u^2) (hu0 : 0 ≤ u) :
    Real.exp (-(3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l)*
      (1+radius d S+Real.log S.card))*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) ≤
      (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
  sorry

end RadiusLens

end OAI
end
