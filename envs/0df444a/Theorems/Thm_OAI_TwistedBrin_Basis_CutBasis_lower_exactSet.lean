-- Prove2me | Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_lower_exactSet
-- name    : OAI.TwistedBrin.Basis.CutBasis.lower_exactSet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:47:35.863355+00:00
-- url     : https://prove2.me/theorems/410b1df7-002f-4f93-ac2a-573223cc9d3c
-- title:
--   OAI.TwistedBrin.Basis.CutBasis.lower_exactSet: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwistedBrin.Basis.CutBasis.lower_exactSet` of [lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisGroundMatching.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisGroundMatching.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwistedBrin.Basis.CutBasis`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory`, `open Classical`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation`, `open scoped MonoidalCategory`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open Set Function`, `open scoped Pointwise`, `open OrderListChains OrderChains`):
--
--   ```lean
--   lemma lower_exactSet [Nonempty S] (C : CutBasis ρ) (n : ℕ)
--       (h : 2*(2*2^(n+2)+1) ≤ rank ρ C.val) : ExactSet (CutBasis ρ) (Set.Iio C) n
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwistedBrin.Basis.rank` (definitions bundle `OAIQ66So015` of this split); `OAI.TwistedBrin.Basis.CutBasis` (definitions bundle `OAIQ66So021` of this split); `OAI.OrderChains.ExactSet` (definitions bundle `OAIQ66So025` of this split); `OAI.TwistedBrin.Basis.CutBasis.instPartialOrder` (definitions bundle `OAIQ66So031` of this split).
--
--   **Used by.** The proofs of `OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented` and `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` of this split import it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisGroundMatching.lean (declaration OAI.TwistedBrin.Basis.CutBasis.lower_exactSet)

import Mathlib
import Definitions.Def_OAIQ66So031

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutBasis
lemma lower_exactSet [Nonempty S] (C : CutBasis ρ) (n : ℕ)
    (h : 2*(2*2^(n+2)+1) ≤ rank ρ C.val) : ExactSet (CutBasis ρ) (Set.Iio C) n := by
  sorry

end CutBasis
end TwistedBrin.Basis

end

end OAI
end
