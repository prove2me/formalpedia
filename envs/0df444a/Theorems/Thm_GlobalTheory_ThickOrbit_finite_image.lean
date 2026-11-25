-- Prove2me | Theorems.Thm_GlobalTheory_ThickOrbit_finite_image
-- name    : GlobalTheory.ThickOrbit.finite_image
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:46:53.711041+00:00
-- url     : https://prove2.me/theorems/c77e9e2c-361c-4178-9f8d-35dd6d2feaeb
-- title:
--   Thick Orbit: finite image
-- statement:
--   The Thick Orbit construction uses the finite image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ThickOrbitSelfDualUnramifiedLattice.lean#L129-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ThickOrbitSelfDualUnramifiedLattice.lean#L129-L148

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLattice
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
open GlobalTheory GlobalTheory.ThickOrbit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.ThickOrbit.finite_image (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n m : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (M e : ℕ)
    (A : AddSubgroup (Fin m → Fin n → E))
    (hA : ∀ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) → algebraMap F E ((ϖ : F) ^ M) • w ∈ A)
    (S : Set (Fin m → Fin n → E)) (hS : ∀ x ∈ S, ∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) :
    ((QuotientAddGroup.mk : _ → _ ⧸ A) '' S).Finite := by sorry
