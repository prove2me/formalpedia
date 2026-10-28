-- Prove2me | Theorems.Thm_OAI_CapOverlap_cap_ratio_decay
-- name    : OAI.CapOverlap.cap_ratio_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:43:45.417145+00:00
-- url     : https://prove2.me/theorems/b8b1bd44-4e5a-4e01-9411-8e9b37eb1dee
-- title:
--   OAI.CapOverlap.cap_ratio_decay: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CapOverlap.cap_ratio_decay` of [lean/OAI/Geometry/TranslativeCovering/CapOverlap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/CapOverlap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CapOverlap`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens`):
--
--   ```lean
--   lemma cap_ratio_decay {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
--       (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u)
--       (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
--       (σ n).real (halfcap e.val s) ≤ Real.exp (-(n:ℝ)*l*(s-t)/2) *
--         (σ n).real (halfcap e.val t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapGeometry.halfcap`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.σ` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proofs of `OAI.NormalizedCaps.clipped_affinity` and `OAI.SlotGeometry.ratio` of this split import it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/CapOverlap.lean (declaration OAI.CapOverlap.cap_ratio_decay)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
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

namespace CapOverlap
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens

lemma cap_ratio_decay {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val s) ≤ Real.exp (-(n:ℝ)*l*(s-t)/2) *
      (σ n).real (halfcap e.val t) := by
  sorry

end CapOverlap

end OAI
end
