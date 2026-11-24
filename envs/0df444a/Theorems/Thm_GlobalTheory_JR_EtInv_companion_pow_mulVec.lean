-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtInv_companion_pow_mulVec
-- name    : GlobalTheory.JR.EtInv.companion_pow_mulVec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:22:58.788383+00:00
-- url     : https://prove2.me/theorems/47f3efcd-3cda-44b1-8e2b-8a4bf7b127a5
-- title:
--   Et Inv: companion pow mul Vec
-- statement:
--   The Et Inv construction uses the companion pow mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean#L59-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean#L59-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtInv
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}

theorem GlobalTheory.JR.EtInv.companion_pow_mulVec (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) (n : ℕ) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : F) else 0) = ⇑(bb.repr (τ ^ n)) := by sorry
