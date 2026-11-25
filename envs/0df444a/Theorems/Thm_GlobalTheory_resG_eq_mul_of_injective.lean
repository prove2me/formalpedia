-- Prove2me | Theorems.Thm_GlobalTheory_resG_eq_mul_of_injective
-- name    : GlobalTheory.resG_eq_mul_of_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:44:01.405797+00:00
-- url     : https://prove2.me/theorems/894ab655-98d9-4466-9020-5b20a8dc952d
-- title:
--   Global Theory: res G eq mul of injective
-- statement:
--   The Global Theory construction uses the res G eq mul of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L383-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L383-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}

theorem GlobalTheory.resG_eq_mul_of_injective {A B G T A' B' T' : X.Opens} (hA : T ≤ A) (hB : T ≤ B)
    (hG : T ≤ G) (hA' : A' ≤ A) (hB' : B' ≤ B) (hT : T' ≤ T) (kA : T' ≤ A') (kB : T' ≤ B')
    (hi : Function.Injective (resG X hT)) {a : Γ(X, A)} {b : Γ(X, B)} {g : Γ(X, G)}
    (h : resG X kA (resG X hA' a) = resG X (hT.trans hG) g * resG X kB (resG X hB' b)) :
    resG X hA a = resG X hG g * resG X hB b := by sorry
