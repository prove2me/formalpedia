-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule_frobeniusClosure
-- name    : GroundTheory.LocalField.Abstract.mem_fixedModule_frobeniusClosure
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:29.903338+00:00
-- url     : https://prove2.me/theorems/4d96d6ee-2f35-4fbe-a9a3-4bf8bfd19892
-- title:
--   Abstract: mem fixed Module frobenius Closure
-- statement:
--   The Abstract construction uses the mem fixed Module frobenius Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L90-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L90-L101

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.LocalField.Abstract.mem_fixedModule_frobeniusClosure {A : Type*} [CommGroup A] [MulDistribMulAction G A]
    [IsDiscreteModule G A] {a : A} :
    a ∈ fixedModule A (frobeniusClosure d L σ) ↔ a ∈ fixedModule A (L ⊓ d.ker) ∧ σ • a = a := by sorry
