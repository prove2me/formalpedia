-- Prove2me | Theorems.Thm_GlobalTheory_HL_TupleJac_cont_linearEquiv
-- name    : GlobalTheory.HL.TupleJac.cont_linearEquiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:36.006165+00:00
-- url     : https://prove2.me/theorems/11524a79-8ec0-4904-afb6-999c2d560bba
-- title:
--   Tuple Jac: cont linear Equiv
-- statement:
--   The Tuple Jac construction uses the cont linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TupleJacobianRightMulIsometry.lean#L113-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TupleJacobianRightMulIsometry.lean#L113-L137

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.TupleJac.cont_linearEquiv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (m : ℕ) (φ : (Fin m → Fin n → E) ≃ₗ[E] (Fin m → Fin n → E))
    (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det φ.toLinearMap * L.cj (LinearMap.det φ.toLinearMap)
      = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) (φ '' T) ∧
      cont (tupLat L Λ m) (φ '' T) = (resQ ϖ : ℝ) ^ (-a) * cont (tupLat L Λ m) T := by sorry
