-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningIso_bijective_of_mod_eps
-- name    : GlobalTheory.ThickeningIso.bijective_of_mod_eps
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:05.529817+00:00
-- url     : https://prove2.me/theorems/98662732-8a62-4e4e-ad5c-84c8bc3d26c0
-- title:
--   Thickening Iso: bijective of mod eps
-- statement:
--   The Thickening Iso construction uses the bijective of mod eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEps.lean#L16-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEps.lean#L16-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEps
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
open GlobalTheory GlobalTheory.ThickeningIso

theorem GlobalTheory.ThickeningIso.bijective_of_mod_eps {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by sorry
