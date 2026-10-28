-- Prove2me | Theorems.Thm_OAI_SlotGeometry_ratio
-- name    : OAI.SlotGeometry.ratio
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:46:24.044001+00:00
-- url     : https://prove2.me/theorems/89dba861-070d-4dab-864b-471040a3af93
-- title:
--   OAI.SlotGeometry.ratio: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SlotGeometry.ratio` of [lean/OAI/Geometry/TranslativeCovering/SlotGeometry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/SlotGeometry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SlotGeometry`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps`, `open scoped BigOperators`):
--
--   ```lean
--   lemma ratio {n : ℕ} [NeZero n] (e f g : Sphere n)
--       {l u U t r s k H K P : ℝ} (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
--       (hlr : l ≤ r) (hru : r ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
--       (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
--       (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) (hH : 1 ≤ H)
--       {E F : Set (Sphere n)} (hE : E ⊆ cap f.val r) (hF : F ⊆ cap g.val s)
--       (hraw1 : (intensity e t).real (cap f.val r) ≤ H)
--       (hraw2 : (intensity e t).real (cap g.val s) ≤ H)
--       (hclip1 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap f.val r)) (1/2))
--       (hclip2 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap g.val s)) (1/2))
--       (hslot1 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap f.val r)) (1/2) ≤ (intensity e t).real E)
--       (hslot2 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap g.val s)) (1/2) ≤ (intensity e t).real F) :
--       (intensity e t).real (E ∩ F)/((intensity e t).real E*(intensity e t).real F) ≤
--         4*H*Real.exp ((2*K+P)*Real.log n-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapCost.intensity`, `OAI.ProjectiveCaps.angle`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.cap` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.PatternCross.fine` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/SlotGeometry.lean (declaration OAI.SlotGeometry.ratio)

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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace SlotGeometry
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

lemma ratio {n : ℕ} [NeZero n] (e f g : Sphere n)
    {l u U t r s k H K P : ℝ} (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hlr : l ≤ r) (hru : r ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) (hH : 1 ≤ H)
    {E F : Set (Sphere n)} (hE : E ⊆ cap f.val r) (hF : F ⊆ cap g.val s)
    (hraw1 : (intensity e t).real (cap f.val r) ≤ H)
    (hraw2 : (intensity e t).real (cap g.val s) ≤ H)
    (hclip1 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap f.val r)) (1/2))
    (hclip2 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap g.val s)) (1/2))
    (hslot1 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap f.val r)) (1/2) ≤ (intensity e t).real E)
    (hslot2 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap g.val s)) (1/2) ≤ (intensity e t).real F) :
    (intensity e t).real (E ∩ F)/((intensity e t).real E*(intensity e t).real F) ≤
      4*H*Real.exp ((2*K+P)*Real.log n-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2) := by
  sorry

end SlotGeometry

end OAI
end
