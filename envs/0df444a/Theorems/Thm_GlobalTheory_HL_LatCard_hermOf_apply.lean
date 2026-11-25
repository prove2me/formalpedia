-- Prove2me | Theorems.Thm_GlobalTheory_HL_LatCard_hermOf_apply
-- name    : GlobalTheory.HL.LatCard.hermOf_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:31:48.389312+00:00
-- url     : https://prove2.me/theorems/5f8a6006-61b2-4cb4-92e3-ce76ab198ce4
-- title:
--   Lat Card: herm Of apply
-- statement:
--   The Lat Card construction uses the herm Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexTupleLatticeHermitianLatticeUniformizer.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexTupleLatticeHermitianLatticeUniformizer.lean#L72-L74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatCard
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.LatCard.hermOf_apply (L : LocE F E) (m : ℕ) (x) (a b : Fin m) : hermOf L m x a b =
    if h : a < b then (x.2 ⟨(a, b), h⟩ : E)
    else if h' : b < a then L.cj (x.2 ⟨(b, a), h'⟩ : E) else algebraMap F E (x.1 a : F) := by sorry
