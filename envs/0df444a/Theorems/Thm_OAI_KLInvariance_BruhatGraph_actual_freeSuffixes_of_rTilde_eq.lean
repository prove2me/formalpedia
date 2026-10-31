-- Prove2me | Theorems.Thm_OAI_KLInvariance_BruhatGraph_actual_freeSuffixes_of_rTilde_eq
-- name    : OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T05:51:52.626008+00:00
-- url     : https://prove2.me/theorems/338dedf9-9a0c-4a0a-a90e-b72b2cf1002c
-- title:
--   OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq` of [lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.BruhatGraph`, with `open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths`):
--
--   ```lean
--    theorem actual_freeSuffixes_of_rTilde_eq
--       (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
--         Hecke.rTilde cs' (φ x).val (φ z).val)
--       (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
--         Module.Free (Coefficient (σ := σ))
--           ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
--             (remainingConditions cs a b q (target cs a b e)))) :
--       FreeSuffixes basis hab φ
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.bruhat_refl`, `OAI.KLInvariance.BruhatGraph.Coefficient`, `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.BruhatGraph.polynomialLabel`, `OAI.KLInvariance.BruhatGraph.target`, `OAI.KLInvariance.Graded.polynomialGrading`, `OAI.KLInvariance.Graded.polynomialGrading_decomposition`, `OAI.KLInvariance.Graded.polynomialGrading_monoid`, `OAI.KLInvariance.Graded.polynomialGrading_negative`, `OAI.KLInvariance.TitsSpace.Extended`, `OAI.KLInvariance.TitsSpace.form`, `OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj`, `OAI.KLInvariance.Graded.ModuleData`, `OAI.KLInvariance.MomentGraph.BoundarySheaf` and `OAI.KLInvariance.MomentGraph.GradedSheaf` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.BruhatGraph.FreeSuffixes`, `OAI.KLInvariance.BruhatGraph.chronologicalSchedule`, `OAI.KLInvariance.BruhatGraph.intervalBoundary`, `OAI.KLInvariance.BruhatGraph.remainingConditions` and `OAI.KLInvariance.MomentGraph.GradedSheaf.upwardSubmodule` (definitions bundle `OAIQ124K004` of this split); `OAI.KLInvariance.Hecke.rTilde` (definitions bundle `OAIQ124K006` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval` and `OAI.KLInvariance.intervalOrder` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proof of `OAI.KLInvariance.combinatorial_invariance` of this split imports it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean (declaration OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq)

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K004
import Definitions.Def_OAIQ124K006

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

 theorem actual_freeSuffixes_of_rTilde_eq
    (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val)
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e)))) :
    FreeSuffixes basis hab φ := by
  sorry

end
end KLInvariance.BruhatGraph

end

end OAI
end
