-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_limit_lam
-- name    : GlobalTheory.Reg.Transfer.limit_lam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:50.116702+00:00
-- url     : https://prove2.me/theorems/a5395a19-ed25-4e81-b04c-425eaafd817d
-- title:
--   Transfer: limit lam
-- statement:
--   The Transfer construction uses the limit lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L421-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L421-L441

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]

theorem GlobalTheory.Reg.Transfer.limit_lam (w t nu c' : ℝ) (eO : ℕ) (heO : 0 < eO) (ht : 0 ≤ t) (hc' : 0 ≤ c')
    (h : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) + (⌈(N : ℝ) * c'⌉₊ : ℝ) * t) :
    w ≤ nu + c' * t := by sorry
