-- Prove2me | Theorems.Thm_GlobalTheory_HL_EichlerParams_sm_mul
-- name    : GlobalTheory.HL.EichlerParams.sm_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:57.506114+00:00
-- url     : https://prove2.me/theorems/f15179f8-7618-4c21-9324-d02a9ad02c1a
-- title:
--   Eichler Params: sm mul
-- statement:
--   The Eichler Params construction uses the sm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianSymplecticBasisLocalExtension.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianSymplecticBasisLocalExtension.lean#L44-L46

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianSymplecticBasisLocalExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerParams
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable (L : LocE K R)

theorem GlobalTheory.HL.EichlerParams.sm_mul {a b : K} {x y : R} (hx : Sm L a x) (hy : Sm L b y) : Sm L (a * b) (x * y) := by sorry
