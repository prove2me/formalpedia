-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_isLocalization_away_of_eq_basicOpen
-- name    : GlobalTheory.NormSheafDescent.isLocalization_away_of_eq_basicOpen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:42.900623+00:00
-- url     : https://prove2.me/theorems/0476b1e5-8e0e-4944-9b0e-7f3c84e8e972
-- title:
--   Norm Sheaf Descent: is Localization away of eq basic Open
-- statement:
--   The Norm Sheaf Descent construction uses the is Localization away of eq basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoeffIdealFamilyMapBasicOpen.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoeffIdealFamilyMapBasicOpen.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFormCoefficientIdealMapLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoeffIdealFamilyMapBasicOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent

theorem GlobalTheory.NormSheafDescent.isLocalization_away_of_eq_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (V : X.Opens) (hV : V = X.basicOpen g) (hle : V ≤ U) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    IsLocalization.Away g Γ(X, V) := by sorry
