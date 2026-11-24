-- Prove2me | Theorems.Thm_GlobalTheory_KSp_mem_box_of_forall_dot
-- name    : GlobalTheory.KSp.mem_box_of_forall_dot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:36.600843+00:00
-- url     : https://prove2.me/theorems/3c0dec45-12b4-43ef-ad3f-fb8d1008da14
-- title:
--   KSp: mem box of forall dot
-- statement:
--   The KSp construction uses the mem box of forall dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualBicharacterPairingOfSymmBilinForm.lean#L17-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualBicharacterPairingOfSymmBilinForm.lean#L17-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinForm
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitWeil.FourierPi (box isCompact_box exists_box_subset)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.mem_box_of_forall_dot {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {d : Type} [Fintype d] [DecidableEq d] (ψ : AddChar F ℂ) {t₀ : Fˣ}
    (ht : ψ t₀ ≠ 1) (s : Fˣ) {v : d → F} (hv : ∀ u ∈ box d s, ψ (u ⬝ᵥ v) = 1) :
    v ∈ box d (t₀ * s⁻¹) := by sorry
