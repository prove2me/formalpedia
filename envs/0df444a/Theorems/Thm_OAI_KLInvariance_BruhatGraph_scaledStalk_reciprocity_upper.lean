-- Prove2me | Theorems.Thm_OAI_KLInvariance_BruhatGraph_scaledStalk_reciprocity_upper
-- name    : OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T05:56:01.985002+00:00
-- url     : https://prove2.me/theorems/99f2ea71-b2ec-4800-ad58-af1cc4dda25e
-- title:
--   OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper` of [lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.BruhatGraph`, with `open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths`):
--
--   ```lean
--   theorem scaledStalk_reciprocity_upper {C : Type*} [Field C]
--       (t : C) (ht : t≠0) (a : W) (x : Interval cs a b) :
--       scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)=
--         ∑ᶠ z : Interval cs a b,
--           eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
--             scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.TitsSpace.Extended` and `OAI.KLInvariance.TitsSpace.form` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.BruhatGraph.upperInclusion` and `OAI.KLInvariance.MomentGraph.GraphMap` (definitions bundle `OAIQ124K004` of this split); `OAI.KLInvariance.Hecke.rTilde` (definitions bundle `OAIQ124K006` of this split); `OAI.KLInvariance.BruhatGraph.scaledStalk` (definitions bundle `OAIQ124K011` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval` and `OAI.KLInvariance.intervalOrder` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proofs of `OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq` and `OAI.KLInvariance.combinatorial_invariance` of this split import it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean (declaration OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper)

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K011

section

attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.scaledInterval
theorem scaledStalk_reciprocity_upper {C : Type*} [Field C]
    (t : C) (ht : t≠0) (a : W) (x : Interval cs a b) :
    scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)=
      ∑ᶠ z : Interval cs a b,
        eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
          scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z) := by
  sorry

end
end KLInvariance.BruhatGraph

end

end OAI
end
