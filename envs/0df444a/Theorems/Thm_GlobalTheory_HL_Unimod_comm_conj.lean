-- Prove2me | Theorems.Thm_GlobalTheory_HL_Unimod_comm_conj
-- name    : GlobalTheory.HL.Unimod.comm_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:45.498397+00:00
-- url     : https://prove2.me/theorems/da4ef539-6006-5082-a48e-adec5976388a
-- title:
--   Unimod: comm conj
-- statement:
--   The Unimod construction uses the comm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryGroupOrthogonalComplementUnimodular.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryGroupOrthogonalComplementUnimodular.lean#L59-L66

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HaarInvVolumeConjModularCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryGroupOrthogonalComplementUnimodular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Unimod
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem GlobalTheory.HL.Unimod.comm_conj (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) : ∀ h ∈ H,
    (H ⊓ stabL L Λ).relIndex (MulAut.conj h • (H ⊓ stabL L Λ)) ≠ 0 ∧
      (MulAut.conj h • (H ⊓ stabL L Λ)).relIndex (H ⊓ stabL L Λ) ≠ 0 := by sorry
