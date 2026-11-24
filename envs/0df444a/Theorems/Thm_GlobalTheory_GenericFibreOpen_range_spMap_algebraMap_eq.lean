-- Prove2me | Theorems.Thm_GlobalTheory_GenericFibreOpen_range_spMap_algebraMap_eq
-- name    : GlobalTheory.GenericFibreOpen.range_spMap_algebraMap_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:29.160965+00:00
-- url     : https://prove2.me/theorems/599c88e0-3d8c-402a-85a2-0180be10df62
-- title:
--   Generic Fibre Open: range sp Map algebra Map eq
-- statement:
--   The Generic Fibre Open construction uses the range sp Map algebra Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PreimageGenericFiberIsOpen.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PreimageGenericFiberIsOpen.lean#L8-L22

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
open GlobalTheory GlobalTheory.GenericFibreOpen

theorem GlobalTheory.GenericFibreOpen.range_spMap_algebraMap_eq (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Set.range (spMap (algebraMap O K)) = {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} := by sorry
