-- Prove2me | Theorems.Thm_OAI_RegularProduct_coset_parent_local_nilpotence
-- name    : OAI.RegularProduct.coset_parent_local_nilpotence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:31:55.289028+00:00
-- url     : https://prove2.me/theorems/7ad815a5-378d-450f-8503-d0aa57a35abe
-- title:
--   OAI.RegularProduct.coset_parent_local_nilpotence: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RegularProduct.coset_parent_local_nilpotence` of [lean/OAI/GroupTheory/FiniteType/StandardHomology.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StandardHomology.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RegularProduct`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory`):
--
--   ```lean
--   lemma coset_parent_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
--       ∀ x : ((Rep.standardComplex ℤ G).coinvariantsTensorObj
--         (CosetInduction.cosetRep S (rep G I))).homology (n+1),
--       ∃ k : ℕ, (HomologicalComplex.homologyMap
--         (StandardTensor.coefficientMap (FunctionalTree.parentHom (rep G I) p peq)) (n+1) : _ → _)^[k] x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CosetInduction.cosetRep`, `OAI.FunctionalTree.diagonalRep` and `OAI.FunctionalTree.parentHom` (definitions bundle `OAIQ66So004` of this split); `OAI.StandardTensor.coefficientMap` (definitions bundle `OAIQ66So005` of this split); `OAI.RegularProduct.rep` (definitions bundle `OAIQ66So007` of this split); `OAI.ListChains.UniformFillings` (definitions bundle `OAIQ66So013` of this split).
--
--   **Used by.** The proof of `OAI.SimpleFInftyOvergroups.SplittingTorusModel.products` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StandardHomology.lean (declaration OAI.RegularProduct.coset_parent_local_nilpotence)

import Mathlib
import Definitions.Def_OAIQ66So013

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

open _root_.CategoryTheory _root_.OAI.CategoryTheory

open _root_.CategoryTheory _root_.OAI.CategoryTheory

namespace RegularProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))
variable (p : (G ⧸ S) → G ⧸ S) (peq : ∀ (g : G) (v : G ⧸ S), p (g • v)=g • p v)
variable (pbase : p (QuotientGroup.mk (1 : G)) = QuotientGroup.mk t)

include t ht pbase peq

lemma coset_parent_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : ((Rep.standardComplex ℤ G).coinvariantsTensorObj
      (CosetInduction.cosetRep S (rep G I))).homology (n+1),
    ∃ k : ℕ, (HomologicalComplex.homologyMap
      (StandardTensor.coefficientMap (FunctionalTree.parentHom (rep G I) p peq)) (n+1) : _ → _)^[k] x = 0 := by
  sorry

end RegularProduct

end

end OAI
end
