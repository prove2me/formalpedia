-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_closed_added_tests
-- name    : OAI.CAT0Fillings.ChartGeometry.closed_added_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:45:04.379047+00:00
-- url     : https://prove2.me/theorems/1d077aa9-3c8b-460f-ae19-7fe199f57edb
-- title:
--   OAI.CAT0Fillings.ChartGeometry.closed_added_tests: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.ChartGeometry.closed_added_tests` of [lean/OAI/Geometry/CAT0Fillings/Chord/TestIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Chord/TestIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings.ChartGeometry`, with `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma closed_added_tests (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
--       {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
--       (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
--       (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
--       (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
--       (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
--         (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
--           (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z)) :
--       ∃ G Q : q.Sobolev,
--         (q.inclusion G : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
--           (fun x => (q.inclusion v x)^(2+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
--         (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
--           (fun x => dist o x^2*(q.inclusion v x)^(1+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
--         (q.closedGradient G : _ → _) =ᵐ[q.atlasMeasure]
--           (fun z => Conformal.profileGradient 0 (2+2*β) β κ f (dist o (q.atlasParam z))
--             (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) ∧
--         (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
--           (fun z => Conformal.profileGradient 2 (1+2*β) β κ f (dist o (q.atlasParam z))
--             (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.atlasParam`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.gradient`, `OAI.CAT0Fillings.ChartGeometry.inclusion` and `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.Conformal.profileGradient` (definitions bundle `OAIQ29C0001` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCycle` and `OAI.CAT0Fillings.IsMetricCurrent` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.ChartGeometry.chord_energy` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Chord/TestIdentity.lean (declaration OAI.CAT0Fillings.ChartGeometry.closed_added_tests)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0000
import Definitions.Def_OAIQ29C0001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_added_tests (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z)) :
    ∃ G Q : q.Sobolev,
      (q.inclusion G : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion v x)^(2+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => dist o x^2*(q.inclusion v x)^(1+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.closedGradient G : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => Conformal.profileGradient 0 (2+2*β) β κ f (dist o (q.atlasParam z))
          (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => Conformal.profileGradient 2 (1+2*β) β κ f (dist o (q.atlasParam z))
          (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) := by
  sorry
end CAT0Fillings.ChartGeometry
end

end OAI
end
