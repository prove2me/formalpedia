-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_chval_div
-- name    : GlobalTheory.Reg.Transfer.chval_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:27.190808+00:00
-- url     : https://prove2.me/theorems/25f2df2e-9500-4527-a734-79502c516e72
-- title:
--   Transfer: chval div
-- statement:
--   The Transfer construction uses the chval div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L105-L126

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

theorem GlobalTheory.Reg.Transfer.chval_div (φ : A →+* V) (e : ℕ) (he : 0 < e) (f : FractionRing A) (r : EReal) (h : ChV φ e f r)
    (hr : 0 ≤ r) (a b : A) (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a)
    (hb : φ b ≠ 0) : ∃ w : V, φ a = w * φ b := by sorry
