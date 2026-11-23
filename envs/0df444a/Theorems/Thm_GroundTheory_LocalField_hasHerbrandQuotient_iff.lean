-- Prove2me | Theorems.Thm_GroundTheory_LocalField_hasHerbrandQuotient_iff
-- name    : GroundTheory.LocalField.hasHerbrandQuotient_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:54.58949+00:00
-- url     : https://prove2.me/theorems/3f403d40-692a-457c-9a0c-5c6e508467db
-- title:
--   Local Field: has Herbrand Quotient iff
-- statement:
--   The Local Field construction uses the has Herbrand Quotient iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L91-L97

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

theorem GroundTheory.LocalField.hasHerbrandQuotient_iff (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      Finite (TateZero G M) ∧ Finite (TateNegOne G M) := by sorry
