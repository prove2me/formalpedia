-- Prove2me | Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_localGroup_finitelyPresented
-- name    : OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:34:13.023104+00:00
-- url     : https://prove2.me/theorems/aaf4ba21-ad89-431d-b517-ca3d75c095aa
-- title:
--   OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented` of [lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisCutBasis.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisCutBasis.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwistedBrin.Basis.CutBasis`, with `open _root_.CategoryTheory CategoryTheory.Limits`, `open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory`, `open Classical`, `open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation`, `open scoped MonoidalCategory`, `open _root_.CategoryTheory CategoryTheory.Limits`, `open Set Function`, `open scoped Pointwise`, `open ActionTransport PosetTransport`):
--
--   ```lean
--   theorem localGroup_finitelyPresented [Nonempty S] (hρ : Function.Injective ρ)
--       (ho : Oligomorphic ρ) [Group.IsFinitelyPresented A]
--       (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) :
--       Group.IsFinitelyPresented (localGroup ρ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwistedBrin.Oligomorphic` and `OAI.TwistedBrin.pointwiseStabilizer` (definitions bundle `OAIQ66So009` of this split); `OAI.TwistedBrin.Box` and `OAI.TwistedBrin.localGroup` (definitions bundle `OAIQ66So015` of this split).
--
--   **Used by.** The proofs of `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` and `OAI_TwistedBrin_localGroup_geometric_of_torus_models` of this split import it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisCutBasis.lean (declaration OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented)

import Mathlib
import Definitions.Def_OAIQ66So015

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

theorem localGroup_finitelyPresented [Nonempty S] (hρ : Function.Injective ρ)
    (ho : Oligomorphic ρ) [Group.IsFinitelyPresented A]
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) :
    Group.IsFinitelyPresented (localGroup ρ) := by
  sorry
end TwistedBrin.Basis.CutBasis

open _root_.CategoryTheory CategoryTheory.Limits

end

end OAI
end
