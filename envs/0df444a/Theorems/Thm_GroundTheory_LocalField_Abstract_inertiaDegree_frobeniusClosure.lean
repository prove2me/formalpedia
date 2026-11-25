-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_frobeniusClosure
-- name    : GroundTheory.LocalField.Abstract.inertiaDegree_frobeniusClosure
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:45.692822+00:00
-- url     : https://prove2.me/theorems/11557485-e268-4dc5-a074-76f7dd8268ba
-- title:
--   Abstract: inertia Degree frobenius Closure
-- statement:
--   The Abstract construction uses the inertia Degree frobenius Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L212-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L212-L217

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
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.inertiaDegree_frobeniusClosure (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    inertiaDegree d (frobeniusClosure d L σ) = N := by sorry
