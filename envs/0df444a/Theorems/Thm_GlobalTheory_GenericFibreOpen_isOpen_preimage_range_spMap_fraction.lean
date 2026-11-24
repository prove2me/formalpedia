-- Prove2me | Theorems.Thm_GlobalTheory_GenericFibreOpen_isOpen_preimage_range_spMap_fraction
-- name    : GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:35.006386+00:00
-- url     : https://prove2.me/theorems/df093ea9-4446-46ea-b372-ad332179dd2a
-- title:
--   Generic Fibre Open: is Open preimage range sp Map fraction
-- statement:
--   The Generic Fibre Open construction uses the is Open preimage range sp Map fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PreimageGenericFiberIsOpen.lean#L28-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PreimageGenericFiberIsOpen.lean#L28-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GenericFibreOpen

theorem GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction :
    ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R]
      [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by sorry
