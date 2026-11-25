-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_or_mul_inv_mem_of_natCard_eq_two
-- name    : GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:57.440259+00:00
-- url     : https://prove2.me/theorems/16075ff7-2cc0-46ab-baa4-cbb19e1a4354
-- title:
--   Automorphic: mem or mul inv mem of nat Card eq two
-- statement:
--   The Automorphic construction uses the mem or mul inv mem of nat Card eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

theorem GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two {G : Type*} [CommGroup G] {N : Subgroup G}
    (hN : Nat.card (G ⧸ N) = 2) {t : G} (ht : t ∉ N) (u : G) : u ∈ N ∨ u * t⁻¹ ∈ N := by sorry
