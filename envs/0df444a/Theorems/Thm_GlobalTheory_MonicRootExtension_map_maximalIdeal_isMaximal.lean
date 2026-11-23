-- Prove2me | Theorems.Thm_GlobalTheory_MonicRootExtension_map_maximalIdeal_isMaximal
-- name    : GlobalTheory.MonicRootExtension.map_maximalIdeal_isMaximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:51.300698+00:00
-- url     : https://prove2.me/theorems/ee66e3c4-d905-4f36-809b-bcb5858d4f30
-- title:
--   Monic Root Extension: map maximal Ideal is Maximal
-- statement:
--   The Monic Root Extension construction uses the map maximal Ideal is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRoot.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRoot.lean#L15-L21

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.MonicRootExtension
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))
include hM hirr

theorem GlobalTheory.MonicRootExtension.map_maximalIdeal_isMaximal :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot M))).IsMaximal := by sorry
