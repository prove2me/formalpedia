-- Prove2me | Theorems.Thm_GlobalTheory_SecSpread_spMap_appTop
-- name    : GlobalTheory.SecSpread.spMap_appTop
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:56:37.280292+00:00
-- url     : https://prove2.me/theorems/2fed87ce-3305-4c9a-82c5-acb17869125c
-- title:
--   Sec Spread: sp Map app Top
-- statement:
--   The Sec Spread construction uses the sp Map app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L46-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread

theorem GlobalTheory.SecSpread.spMap_appTop {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (a : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (f a) := by sorry
