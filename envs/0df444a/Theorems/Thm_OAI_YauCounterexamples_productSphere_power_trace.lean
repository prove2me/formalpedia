-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_productSphere_power_trace
-- name    : OAI.YauCounterexamples.productSphere_power_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:25:23.854037+00:00
-- url     : https://prove2.me/theorems/8cf02724-e528-4581-9781-01376bfbb50a
-- title:
--   OAI.YauCounterexamples.productSphere_power_trace: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.productSphere_power_trace` of [lean/OAI/Geometry/SmoothYau/Estimates/ComplexGramTraceSecondMul.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ComplexGramTraceSecondMul.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Module`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   lemma productSphere_power_trace (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
--       (p : Metric.sphere (0:A) 1) (q : Metric.sphere (0:B) 1) (a b : A) (c d : B)
--       (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
--       (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
--       (hc : inner ℝ c c = 1) (hd : inner ℝ d d = 1) (hcd : inner ℝ c d = 0) :
--       complexGramTrace e (fun v w => fderiv ℝ (fun y => fderiv ℝ
--         (fun z => productSphere_fstPower p (planarLinear a b) k z*
--           productSphere_sndPower q (planarLinear c d) l z) y w) 0 v) =
--         -((k:ℂ)*((k:ℂ)+(n:ℂ)-1)+(l:ℂ)*((l:ℂ)+(m:ℂ)-1))*
--           (planarLinear a b p)^k*(planarLinear c d q)^l
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.complexGramTrace` and `OAI.YauCounterexamples.planarLinear` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productSphere_fstPower` and `OAI.YauCounterexamples.productSphere_sndPower` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.Euclidean` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay`, `OAI_YauCounterexamples_threePower_eigen` and `OAI.YauCounterexamples.three_wave_residual_support` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ComplexGramTraceSecondMul.lean (declaration OAI.YauCounterexamples.productSphere_power_trace)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] in
lemma productSphere_power_trace (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (q : Metric.sphere (0:B) 1) (a b : A) (c d : B)
    (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hc : inner ℝ c c = 1) (hd : inner ℝ d d = 1) (hcd : inner ℝ c d = 0) :
    complexGramTrace e (fun v w => fderiv ℝ (fun y => fderiv ℝ
      (fun z => productSphere_fstPower p (planarLinear a b) k z*
        productSphere_sndPower q (planarLinear c d) l z) y w) 0 v) =
      -((k:ℂ)*((k:ℂ)+(n:ℂ)-1)+(l:ℂ)*((l:ℂ)+(m:ℂ)-1))*
        (planarLinear a b p)^k*(planarLinear c d q)^l := by
  sorry
end YauCounterexamples
end

end OAI
end
