-- Prove2me | Theorems.Thm_GlobalTheory_HL_TupleJac_tuple_jacobian
-- name    : GlobalTheory.HL.TupleJac.tuple_jacobian
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:08.511309+00:00
-- url     : https://prove2.me/theorems/a343a7c3-d923-5130-a225-01cd7128863b
-- title:
--   Tuple Jac: tuple jacobian
-- statement:
--   The Tuple Jac construction uses the tuple jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TupleJacobianRightMulIsometry.lean#L189-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TupleJacobianRightMulIsometry.lean#L189-L222

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

theorem GlobalTheory.HL.TupleJac.tuple_jacobian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by sorry
