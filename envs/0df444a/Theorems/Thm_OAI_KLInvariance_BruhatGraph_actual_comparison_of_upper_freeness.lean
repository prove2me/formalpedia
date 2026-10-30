-- Prove2me | Theorems.Thm_OAI_KLInvariance_BruhatGraph_actual_comparison_of_upper_freeness
-- name    : OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T05:53:38.733991+00:00
-- url     : https://prove2.me/theorems/c534ef1b-ccad-4fe5-8047-8245ed31dd46
-- title:
--   OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness` of [lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.BruhatGraph`, with `open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths`):
--
--   ```lean
--    theorem actual_comparison_of_upper_freeness
--       (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
--         Module.Free (Coefficient (σ := σ))
--           ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
--             (remainingConditions cs a b q (target cs a b e))))
--       {t : ℝ} (ht : 0<t) (ht1 : t<1) :
--       (fun x : Interval cs a b => scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)) ≤
--         dispatch (source cs a b) (target cs a b) (t⁻¹-t)
--           (fun x => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x))
--           (transportedSchedule φ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.bruhat_refl`, `OAI.KLInvariance.BruhatGraph.Coefficient`, `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.BruhatGraph.polynomialLabel`, `OAI.KLInvariance.BruhatGraph.source`, `OAI.KLInvariance.BruhatGraph.target`, `OAI.KLInvariance.Graded.polynomialGrading`, `OAI.KLInvariance.Graded.polynomialGrading_decomposition`, `OAI.KLInvariance.Graded.polynomialGrading_monoid`, `OAI.KLInvariance.Graded.polynomialGrading_negative`, `OAI.KLInvariance.TitsSpace.Extended`, `OAI.KLInvariance.TitsSpace.form`, `OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj`, `OAI.KLInvariance.Graded.ModuleData`, `OAI.KLInvariance.MomentGraph.BoundarySheaf` and `OAI.KLInvariance.MomentGraph.GradedSheaf` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.BruhatGraph.chronologicalSchedule`, `OAI.KLInvariance.BruhatGraph.intervalBoundary`, `OAI.KLInvariance.BruhatGraph.remainingConditions`, `OAI.KLInvariance.BruhatGraph.transportedSchedule`, `OAI.KLInvariance.BruhatGraph.upperInclusion`, `OAI.KLInvariance.MomentGraph.GradedSheaf.upwardSubmodule` and `OAI.KLInvariance.MomentGraph.GraphMap` (definitions bundle `OAIQ124K004` of this split); `OAI.KLInvariance.SchedulePaths.dispatch` (definitions bundle `OAIQ124K007` of this split); `OAI.KLInvariance.BruhatGraph.scaledStalk` (definitions bundle `OAIQ124K011` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval` and `OAI.KLInvariance.intervalOrder` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proof of `OAI.KLInvariance.combinatorial_invariance` of this split imports it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean (declaration OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness)

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b)
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section

 theorem actual_comparison_of_upper_freeness
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e))))
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    (fun x : Interval cs a b => scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)) ≤
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (fun x => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x))
        (transportedSchedule φ) := by
  sorry

end
end KLInvariance.BruhatGraph

end

end OAI
end
