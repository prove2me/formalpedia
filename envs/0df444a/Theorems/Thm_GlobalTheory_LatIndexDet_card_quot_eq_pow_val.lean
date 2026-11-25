-- Prove2me | Theorems.Thm_GlobalTheory_LatIndexDet_card_quot_eq_pow_val
-- name    : GlobalTheory.LatIndexDet.card_quot_eq_pow_val
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:23.253652+00:00
-- url     : https://prove2.me/theorems/ab28761f-034f-4b44-bd04-a4ebe5f1f90a
-- title:
--   Lat Index Det: card quot eq pow val
-- statement:
--   The Lat Index Det construction uses the card quot eq pow val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapDetRestrict.lean#L89-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapDetRestrict.lean#L89-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapDetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LatIndexDet

theorem GlobalTheory.LatIndexDet.card_quot_eq_pow_val : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (V : Type) [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [FiniteDimensional E V] (N : Submodule O V), N.FG → Submodule.span E (N : Set V) = ⊤ → ∀ T : V →ₗ[E] V, LinearMap.det T ≠ 0 → (∀ x ∈ N, T x ∈ N) → (Nat.card (↥N ⧸ (N.map (T.restrictScalars O)).comap N.subtype) : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (LinearMap.det T) := by sorry
