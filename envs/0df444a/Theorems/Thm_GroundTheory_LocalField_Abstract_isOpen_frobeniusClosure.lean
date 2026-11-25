-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_isOpen_frobeniusClosure
-- name    : GroundTheory.LocalField.Abstract.isOpen_frobeniusClosure
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:41.666983+00:00
-- url     : https://prove2.me/theorems/3292001e-fd57-4c33-b13a-226d1a6750a3
-- title:
--   Abstract: is Open frobenius Closure
-- statement:
--   The Abstract construction uses the is Open frobenius Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L187-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L187-L208

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
variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.isOpen_frobeniusClosure (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    IsOpen (frobeniusClosure d L σ : Set G) := by sorry
