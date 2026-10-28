-- Prove2me | Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_localGroup_geometric_of_certificates
-- name    : OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:34:54.161996+00:00
-- url     : https://prove2.me/theorems/1200e8f5-fd13-4785-add8-287b71bdeabe
-- title:
--   OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` of [lean/OAI/GroupTheory/FiniteType/OrderChainsExactSubtypeOfExactSet.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/OrderChainsExactSubtypeOfExactSet.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwistedBrin.Basis.CutBasis`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open EquivariantOrderChains ActionTransport PosetTransport`):
--
--   ```lean
--   theorem localGroup_geometric_of_certificates [Nonempty S]
--       (hρ : Function.Injective ρ) (ho : Oligomorphic ρ)
--       [Group.IsFinitelyPresented A]
--       (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
--       (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
--         IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1))) :
--       SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RegularProductR.rep` (definitions bundle `OAIQ66So003` of this split); `OAI.TwistedBrin.Oligomorphic` and `OAI.TwistedBrin.pointwiseStabilizer` (definitions bundle `OAIQ66So009` of this split); `OAI.TwistedBrin.Box` and `OAI.TwistedBrin.localGroup` (definitions bundle `OAIQ66So015` of this split); `OAI.SimpleFInftyOvergroups.HasTypeFInfty` (the published bundle `Def_SimpleOvergroups`).
--
--   **Used by.** The proof of `OAI.StageGeometry.localGroup_geometric_of_binary_ring_data` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/OrderChainsExactSubtypeOfExactSet.lean (declaration OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates)

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So003
import Definitions.Def_OAIQ66So015

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

namespace TwistedBrin.Basis.CutBasis
open EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

theorem localGroup_geometric_of_certificates [Nonempty S]
    (hρ : Function.Injective ρ) (ho : Oligomorphic ρ)
    [Group.IsFinitelyPresented A]
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1))) :
    SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ) := by
  sorry
end TwistedBrin.Basis.CutBasis

end
end

end OAI
end
