-- Prove2me | Theorems.Thm_OAI_KLInvariance_BruhatGraph_actual_endpoint_of_rTilde_eq
-- name    : OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T05:53:23.262994+00:00
-- url     : https://prove2.me/theorems/84618f90-4e74-4faf-8781-e5488503f489
-- title:
--   OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq` of [lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.BruhatGraph`, with `open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths`):
--
--   ```lean
--    theorem actual_endpoint_of_rTilde_eq
--       (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
--         Hecke.rTilde cs' (φ x).val (φ z).val)
--       {t : ℝ} (ht : 0<t) (ht1 : t<1) :
--       scheduleState cs a b basis hab (intervalBoundary basis hab) t []=
--         dispatch (source cs a b) (target cs a b) (t⁻¹-t)
--           (scheduleState cs a b basis hab (intervalBoundary basis hab) t (chronologicalSchedule φ))
--           (chronologicalSchedule φ).reverse
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.source`, `OAI.KLInvariance.BruhatGraph.target`, `OAI.KLInvariance.TitsSpace.Extended` and `OAI.KLInvariance.TitsSpace.form` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.BruhatGraph.chronologicalSchedule` and `OAI.KLInvariance.BruhatGraph.intervalBoundary` (definitions bundle `OAIQ124K004` of this split); `OAI.KLInvariance.Hecke.rTilde` (definitions bundle `OAIQ124K006` of this split); `OAI.KLInvariance.SchedulePaths.dispatch` (definitions bundle `OAIQ124K007` of this split); `OAI.KLInvariance.BruhatGraph.scheduleState` (definitions bundle `OAIQ124K011` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval` and `OAI.KLInvariance.intervalOrder` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proof of `OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq` of this split imports it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean (declaration OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq)

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

 theorem actual_endpoint_of_rTilde_eq
    (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t []=
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (scheduleState cs a b basis hab (intervalBoundary basis hab) t (chronologicalSchedule φ))
        (chronologicalSchedule φ).reverse := by
  sorry

end
end KLInvariance.BruhatGraph

end

end OAI
end
