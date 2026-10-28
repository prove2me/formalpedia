-- Prove2me | Theorems.Thm_OAI_OrderBrown_vanishing
-- name    : OAI.OrderBrown.vanishing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:37:05.39037+00:00
-- url     : https://prove2.me/theorems/2ef63c63-a57c-4a06-a34d-89e2cef02923
-- title:
--   OAI.OrderBrown.vanishing: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.OrderBrown.vanishing` of [lean/OAI/GroupTheory/FiniteType/EquivariantOrderChains.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/EquivariantOrderChains.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.OrderBrown`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory`, `open Classical`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation`, `open scoped MonoidalCategory`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open Set Function`, `open scoped Pointwise`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open scoped MonoidalCategory`, `open OrderChainComplex EquivariantOrderChains`):
--
--   ```lean
--   theorem vanishing (N : ℕ)
--       (he : ∀ i ≤ N+1, OrderChains.ExactIn P i)
--       (hf : ∀ n : ℕ, Finite (OrbitCoefficients.Orbits (G := G) (simplexSet P n)))
--       (hfg : ∀ n : ℕ, ∀ s : simplexSet P n, Group.FG (MulAction.stabilizer G s))
--       (hz : ∀ n : ℕ, ∀ s : simplexSet P n, ∀ (J : Type) (j : ℕ),
--         IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer G s) J) (j+1))) :
--       IsZero (groupHomology (RegularProductR.rep ℤ G I) (N+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RegularProductR.rep` (definitions bundle `OAIQ66So003` of this split); `OAI.OrderListChains.Simplex` (definitions bundle `OAIQ66So004` of this split); `OAI.OrbitCoefficients.Orbits` (definitions bundle `OAIQ66So007` of this split); `OAI.EquivariantOrderChains.simplexAction` and `OAI.OrderChainComplex.simplexSet` (definitions bundle `OAIQ66So018` of this split); `OAI.OrderChains.ExactIn` (definitions bundle `OAIQ66So025` of this split).
--
--   **Used by.** The proof of `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/EquivariantOrderChains.lean (declaration OAI.OrderBrown.vanishing)

import Mathlib
import Definitions.Def_OAIQ66So025

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
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
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex

attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule

end EquivariantOrderChains

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace OrderBrown
attribute [-instance] AddCommGroup.toIntModule
open OrderChainComplex EquivariantOrderChains
variable {G P I : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] [Nonempty P]

theorem vanishing (N : ℕ)
    (he : ∀ i ≤ N+1, OrderChains.ExactIn P i)
    (hf : ∀ n : ℕ, Finite (OrbitCoefficients.Orbits (G := G) (simplexSet P n)))
    (hfg : ∀ n : ℕ, ∀ s : simplexSet P n, Group.FG (MulAction.stabilizer G s))
    (hz : ∀ n : ℕ, ∀ s : simplexSet P n, ∀ (J : Type) (j : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer G s) J) (j+1))) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (N+1)) := by
  sorry
end OrderBrown

end

end OAI
end
