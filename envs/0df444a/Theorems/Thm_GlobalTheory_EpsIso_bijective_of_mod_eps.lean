-- Prove2me | Theorems.Thm_GlobalTheory_EpsIso_bijective_of_mod_eps
-- name    : GlobalTheory.EpsIso.bijective_of_mod_eps
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:12:29.905793+00:00
-- url     : https://prove2.me/theorems/8790d51e-5788-5f33-a20b-def4c995ac04
-- title:
--   Eps Iso: bijective of mod eps
-- statement:
--   The Eps Iso construction uses the bijective of mod eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfIdModEpsThickening.lean#L71-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfIdModEpsThickening.lean#L71-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso

theorem GlobalTheory.EpsIso.bijective_of_mod_eps {K : Type} [Field K] {B C D : Type} [CommRing B] [CommRing C]
    [CommRing D] (a : DualNumber K →+* B) (φ : B →+* C) (jB : B →+* D) (jC : C →+* D)
    (hφ : ∀ b, jC (φ b) = jB b) (hs : Function.Surjective jB) (hfl : (φ.comp a).Flat)
    (hB : RingHom.ker jB = Ideal.span {a DualNumber.eps})
    (hC : RingHom.ker jC = Ideal.span {φ (a DualNumber.eps)}) : Function.Bijective φ := by sorry
