-- Prove2me | Theorems.Thm_GroundTheory_Global_card_smul_sub_normHom_mem
-- name    : GroundTheory.Global.card_smul_sub_normHom_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:42.998517+00:00
-- url     : https://prove2.me/theorems/3f96120d-64f6-4a81-b34d-94b62d51d013
-- title:
--   Global: card smul sub norm Hom mem
-- statement:
--   The Global construction uses the card smul sub norm Hom mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L82-L89

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}
variable [Fintype G]

theorem GroundTheory.Global.card_smul_sub_normHom_mem (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : M) :
    (Fintype.card G : ℤ) • x - normHom ρ x ∈ (cycSub ρ σ).range := by sorry
