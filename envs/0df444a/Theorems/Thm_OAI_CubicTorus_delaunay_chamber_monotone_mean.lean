-- Prove2me | Theorems.Thm_OAI_CubicTorus_delaunay_chamber_monotone_mean
-- name    : OAI.CubicTorus.delaunay_chamber_monotone_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:36:48.925358+00:00
-- url     : https://prove2.me/theorems/ccb81919-cbb7-49fd-b3fc-11f29cc4e8bc
-- title:
--   OAI.CubicTorus.delaunay_chamber_monotone_mean: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.delaunay_chamber_monotone_mean` of [lean/OAI/Geometry/CubicTorus/Reflection/DelaunayPeriodicMoments.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/DelaunayPeriodicMoments.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem delaunay_chamber_monotone_mean {r p : ℝ → ℝ} {a b c : ℝ}
--       (ha : 0<a) (hab : a<b) (hc : c=0 ∨ c=1/2)
--       (hr : ∀ t,HasDerivAt r (p t) t)
--       (hrp : Function.Periodic r 1) (he : ∀ t,r (-t)=r t)
--       (hneg : ∀ t∈Ioo c (c+1/2),p t<0)
--       (hf : ∀ t,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) :
--       (a^2+b^2)/2≤∫ t in (0 : ℝ)..1,r t^2
--   ```
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_first_transition_standard` and `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/DelaunayPeriodicMoments.lean (declaration OAI.CubicTorus.delaunay_chamber_monotone_mean)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set MeasureTheory Filter
namespace CubicTorus

theorem delaunay_chamber_monotone_mean {r p : ℝ → ℝ} {a b c : ℝ}
    (ha : 0<a) (hab : a<b) (hc : c=0 ∨ c=1/2)
    (hr : ∀ t,HasDerivAt r (p t) t)
    (hrp : Function.Periodic r 1) (he : ∀ t,r (-t)=r t)
    (hneg : ∀ t∈Ioo c (c+1/2),p t<0)
    (hf : ∀ t,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) :
    (a^2+b^2)/2≤∫ t in (0 : ℝ)..1,r t^2 := by
  sorry

end CubicTorus

end
end

end OAI
end
