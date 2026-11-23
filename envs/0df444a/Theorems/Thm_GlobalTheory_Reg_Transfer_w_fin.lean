-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_w_fin
-- name    : GlobalTheory.Reg.Transfer.w_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:59.652797+00:00
-- url     : https://prove2.me/theorems/3c228ac1-032e-4f0e-ab57-26b2ae3c40d2
-- title:
--   Transfer: w fin
-- statement:
--   The Transfer construction uses the w fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L405-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L405-L419

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

theorem GlobalTheory.Reg.Transfer.w_fin {φ : A →+* V} {e : ℕ} {fw : FractionRing A} {W : EReal} (hW : ChV φ e fw W) (P yw : A)
    (hrel : fw⁻¹ * algebraMap A (FractionRing A) P = algebraMap A (FractionRing A) yw) (hfw0 : fw ≠ 0)
    (hP : φ P ≠ 0) : ∃ w : ℝ, W = (w : EReal) := by sorry
