-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_round_pair_rank_transfer
-- name    : OAI.YauCounterexamples.round_pair_rank_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:46:57.159066+00:00
-- url     : https://prove2.me/theorems/6658f497-5da6-4ab4-abc5-dab53ee1b896
-- title:
--   OAI.YauCounterexamples.round_pair_rank_transfer: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.round_pair_rank_transfer` of [lean/OAI/Geometry/SmoothYau/Geometry/CoordinateGradientPairCongrNhds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/CoordinateGradientPairCongrNhds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   lemma round_pair_rank_transfer (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
--       (p : Sphere d) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
--       (hr : Complex.normSq (planarLinear a b p) < 1)
--       (hi : ((planarLinear a b p)^n).im ≠ 0) {H : Euclidean d → ℝ × ℝ}
--       (he : H =ᶠ[𝓝 0] (roundPowerRadius a b n ∘ (chartAt (Euclidean d) p).symm)) :
--       ContDiffAt ℝ 1 H 0 ∧ Function.Surjective (fderiv ℝ H 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.planarLinear` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.roundPowerRadius` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/CoordinateGradientPairCongrNhds.lean (declaration OAI.YauCounterexamples.round_pair_rank_transfer)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
lemma round_pair_rank_transfer (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (p : Sphere d) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hr : Complex.normSq (planarLinear a b p) < 1)
    (hi : ((planarLinear a b p)^n).im ≠ 0) {H : Euclidean d → ℝ × ℝ}
    (he : H =ᶠ[𝓝 0] (roundPowerRadius a b n ∘ (chartAt (Euclidean d) p).symm)) :
    ContDiffAt ℝ 1 H 0 ∧ Function.Surjective (fderiv ℝ H 0) := by
  sorry

end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end
