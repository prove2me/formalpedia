-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natCard_tateZero_eq
-- name    : GroundTheory.LocalField.natCard_tateZero_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:05.984262+00:00
-- url     : https://prove2.me/theorems/c7fa408f-57f9-4d55-bc76-5b768edbbf6a
-- title:
--   Local Field: nat Card tate Zero eq
-- statement:
--   The Local Field construction uses the nat Card tate Zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L63-L70

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}

theorem GroundTheory.LocalField.natCard_tateZero_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateZero G M) =
      Nat.card (CycTateZero (Representation.ofMulDistribMulAction G M) σ) := by sorry
