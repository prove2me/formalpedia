-- Prove2me | Theorems.Thm_GlobalTheory_MonicRootExtension_isLocalHom
-- name    : GlobalTheory.MonicRootExtension.isLocalHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:42.663179+00:00
-- url     : https://prove2.me/theorems/171031d4-1d7c-4a1c-b326-794b393dbfda
-- title:
--   Monic Root Extension: is Local Hom
-- statement:
--   The Monic Root Extension construction uses the is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRoot.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRoot.lean#L37-L43

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

theorem GlobalTheory.MonicRootExtension.isLocalHom [IsLocalRing (AdjoinRoot M)] : IsLocalHom (algebraMap A (AdjoinRoot M)) := by sorry
