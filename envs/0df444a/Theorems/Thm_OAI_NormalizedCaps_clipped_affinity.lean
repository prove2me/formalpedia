-- Prove2me | Theorems.Thm_OAI_NormalizedCaps_clipped_affinity
-- name    : OAI.NormalizedCaps.clipped_affinity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:44:01.889991+00:00
-- url     : https://prove2.me/theorems/8670208a-fe80-44c0-b265-beb2601dc74f
-- title:
--   OAI.NormalizedCaps.clipped_affinity: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NormalizedCaps.clipped_affinity` of [lean/OAI/Geometry/TranslativeCovering/NormalizedCaps.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/NormalizedCaps.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NormalizedCaps`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open MeasureTheory SphericalLaw CapCost CapAffinity ProjectiveCaps`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   lemma clipped_affinity {n : ℕ} [NeZero n] {I : Type u_1} (e : Sphere n)
--       (axes : I → Sphere n) (τ : I → ℝ) {l u U t k H c : ℝ}
--       (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
--       (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u) (huU : u ≤ U)
--       (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
--       (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l)
--       (hH : 1 ≤ H) (hraw : ∀ i,(intensity e t).real (cap (axes i).val (τ i)) ≤ H)
--       (hc : 0 ≤ c) (hca : c ≤ (2*l*k/Real.pi^2)/4) (hcy : c ≤ 1/8) (i j : I) :
--       let μ := intensity e t
--       let C := fun i => cap (axes i).val (τ i)
--       let s := fun i => -Real.log (min (μ.real (C i)) (1/2))
--       μ.real (C i ∩ C j)/Real.sqrt (min (μ.real (C i)) (1/2)*min (μ.real (C j)) (1/2)) ≤
--         4*H*Real.exp (-c*(costDist n (fun i => (axes i).val) s i j)^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapCost.intensity`, `OAI.ProjectiveCaps.costDist`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.cap` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.WitnessConstruction.shell` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/NormalizedCaps.lean (declaration OAI.NormalizedCaps.clipped_affinity)

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

universe u_1

namespace NormalizedCaps
open MeasureTheory SphericalLaw CapCost CapAffinity ProjectiveCaps
open scoped ENNReal NNReal

lemma clipped_affinity {n : ℕ} [NeZero n] {I : Type u_1} (e : Sphere n)
    (axes : I → Sphere n) (τ : I → ℝ) {l u U t k H c : ℝ}
    (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l)
    (hH : 1 ≤ H) (hraw : ∀ i,(intensity e t).real (cap (axes i).val (τ i)) ≤ H)
    (hc : 0 ≤ c) (hca : c ≤ (2*l*k/Real.pi^2)/4) (hcy : c ≤ 1/8) (i j : I) :
    let μ := intensity e t
    let C := fun i => cap (axes i).val (τ i)
    let s := fun i => -Real.log (min (μ.real (C i)) (1/2))
    μ.real (C i ∩ C j)/Real.sqrt (min (μ.real (C i)) (1/2)*min (μ.real (C j)) (1/2)) ≤
      4*H*Real.exp (-c*(costDist n (fun i => (axes i).val) s i j)^2) := by
  sorry

end NormalizedCaps

end OAI
end
