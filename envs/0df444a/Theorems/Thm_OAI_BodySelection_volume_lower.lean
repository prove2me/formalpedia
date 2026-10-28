-- Prove2me | Theorems.Thm_OAI_BodySelection_volume_lower
-- name    : OAI.BodySelection.volume_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:42:25.75214+00:00
-- url     : https://prove2.me/theorems/47355a2b-4c63-46cf-a546-706b4756e6b3
-- title:
--   OAI.BodySelection.volume_lower: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BodySelection.volume_lower` of [lean/OAI/Geometry/TranslativeCovering/BodySelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/BodySelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BodySelection`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Metric MeasureTheory Filter SourceParameters LocalizationRates PatternEnumeration SourceLocalization SphericalLaw`, `open scoped ENNReal Topology Classical`):
--
--   ```lean
--   lemma volume_lower {n : ℕ} [NeZero n] [Fact (2≤n)] (e : Sphere n)
--       (hβ : 0<β n) (houter : (β n/a)^n≤3) :
--       1/10 ≤ (BodyVolume.law e a).real {U | 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U)}
--   ```
--
--   **Definitions.** The statement is written with `OAI.BodySelection.Space`, `OAI.BodyVolume.law`, `OAI.LocalizationRates.β`, `OAI.PoissonConfig.Config`, `OAI.RandomBody.body`, `OAI.SourceParameters.a`, `OAI.SourceParameters.b`, `OAI.SourceParameters.v`, `OAI.SphericalLaw.Space` and `OAI.SphericalLaw.Sphere` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.TranslativeCovering.main` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/BodySelection.lean (declaration OAI.BodySelection.volume_lower)

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
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
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
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace BodySelection
open Set Metric MeasureTheory Filter SourceParameters LocalizationRates PatternEnumeration SourceLocalization SphericalLaw
open scoped ENNReal Topology Classical
lemma volume_lower {n : ℕ} [NeZero n] [Fact (2≤n)] (e : Sphere n)
    (hβ : 0<β n) (houter : (β n/a)^n≤3) :
    1/10 ≤ (BodyVolume.law e a).real {U | 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U)} := by
  sorry

end BodySelection

end OAI
end
