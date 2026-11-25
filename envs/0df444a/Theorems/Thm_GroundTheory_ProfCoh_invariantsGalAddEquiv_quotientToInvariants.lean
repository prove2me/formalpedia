-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_invariantsGalAddEquiv_quotientToInvariants
-- name    : GroundTheory.ProfCoh.invariantsGalAddEquiv_quotientToInvariants
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:25.134797+00:00
-- url     : https://prove2.me/theorems/68fea0ab-8454-4509-99d8-e62da89bac21
-- title:
--   Prof Coh: invariants Gal Add Equiv quotient To Invariants
-- statement:
--   The Prof Coh construction uses the invariants Gal Add Equiv quotient To Invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L101-L109

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open IntermediateField InfiniteGalois
universe u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] (U : OpenNormalSubgroup Gal(L/K))

theorem GroundTheory.ProfCoh.invariantsGalAddEquiv_quotientToInvariants (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (x : Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsGalAddEquiv U (((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q x) =
      quotientEquivGal U q (invariantsGalAddEquiv U x) := by sorry
