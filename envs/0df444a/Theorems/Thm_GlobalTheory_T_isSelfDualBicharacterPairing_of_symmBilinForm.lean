-- Prove2me | Theorems.Thm_GlobalTheory_T_isSelfDualBicharacterPairing_of_symmBilinForm
-- name    : GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:32.945307+00:00
-- url     : https://prove2.me/theorems/46e1e8fe-4dab-41bd-9255-89a5249624a2
-- title:
--   T: is Self Dual Bicharacter Pairing of symm Bilin Form
-- statement:
--   The T construction uses the is Self Dual Bicharacter Pairing of symm Bilin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualBicharacterPairingOfSymmBilinFormStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualBicharacterPairingOfSymmBilinFormStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by sorry
