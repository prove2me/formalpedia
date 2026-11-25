-- Prove2me | Theorems.Thm_GlobalTheory_HL_VolPerp_key
-- name    : GlobalTheory.HL.VolPerp.key
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:49.825052+00:00
-- url     : https://prove2.me/theorems/8a533a5a-36d3-4e7a-9427-1d0d08f163d2
-- title:
--   Vol Perp: key
-- statement:
--   The Vol Perp construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean#L83-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean#L83-L158

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRat
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.VolPerp
open GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.HL.VolPerp.key (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') {m : ℕ} (y : Fin m → Fin n → E) (hy : LinearIndependent E y)
    {Y Z : Submodule L.O (Fin n → E)}
    (hY : Y = (Submodule.span E (Set.range y)).restrictScalars L.O)
    (hZ : Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O) :
    (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧
    (Λ.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup =
    (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup := by sorry
