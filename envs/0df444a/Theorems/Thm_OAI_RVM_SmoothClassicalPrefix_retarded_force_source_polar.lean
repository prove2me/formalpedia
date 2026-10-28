-- Prove2me | Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_retarded_force_source_polar
-- name    : OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:21:24.336253+00:00
-- url     : https://prove2.me/theorems/08a1d0dd-8f70-44c0-83d4-d9404e01c347
-- title:
--   OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar` of [lean/OAI/Analysis/VlasovMaxwell/Regularity/IntegralBallPolarFlip.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/IntegralBallPolarFlip.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma SmoothClassicalPrefix.retarded_force_source_polar {d : Datum} {s : Solution} {H t : ℝ}
--       (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (htH : t<H)
--       (x a : Vec) (ha : ‖a‖<1) :
--       s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
--         (4*Real.pi)⁻¹ • ∫n : Sphere,∫σ in Ioo (0:ℝ) t,
--           (1-dot n.1 a) • ∫v : Vec,s.f (σ,(x-(t-σ) • n.1,v)) •
--             normalisedSignedForce (t-σ) a (velocity v) n.1
--               (sourceAcceleration s (σ,(x-(t-σ) • n.1,v))) ∂volume ∂volume ∂sphereMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.Sphere`, `OAI.RVM.boundaryLorentzForce`, `OAI.RVM.datumBoundarySolution`, `OAI.RVM.normalisedSignedForce`, `OAI.RVM.sourceAcceleration` and `OAI.RVM.sphereMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross`, `OAI.RVM.dot` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direction_count_bound`, `OAI.RVM.Admissible.force_bulk_uniform`, `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable` and `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_label` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/IntegralBallPolarFlip.lean (declaration OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.retarded_force_source_polar {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (htH : t<H)
    (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫σ in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (σ,(x-(t-σ) • n.1,v)) •
          normalisedSignedForce (t-σ) a (velocity v) n.1
            (sourceAcceleration s (σ,(x-(t-σ) • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  sorry

end RVM

end

end OAI
end
