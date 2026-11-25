-- Prove2me | Theorems.Thm_GlobalTheory_T_preimage_generic_fiber_isOpen
-- name    : GlobalTheory.T.preimage_generic_fiber_isOpen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:31.187121+00:00
-- url     : https://prove2.me/theorems/8303b30d-a40d-426c-aba4-d3fef4cf3373
-- title:
--   T: preimage generic fiber is Open
-- statement:
--   The T construction uses the preimage generic fiber is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PreimageGenericFiberIsOpenStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PreimageGenericFiberIsOpenStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpen
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.preimage_generic_fiber_isOpen : ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R] [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by sorry
