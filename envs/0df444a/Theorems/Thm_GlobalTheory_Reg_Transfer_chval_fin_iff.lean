-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_iff
-- name    : GlobalTheory.Reg.Transfer.chval_fin_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:40.324432+00:00
-- url     : https://prove2.me/theorems/0566021b-c907-44db-8890-50299dd895f1
-- title:
--   Transfer: chval fin iff
-- statement:
--   The Transfer construction uses the chval fin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L162-L176

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

theorem GlobalTheory.Reg.Transfer.chval_fin_iff (φ : A →+* V) (e : ℕ) (f : FractionRing A) (u : ℝ) :
    ChV φ e f (u : EReal) ↔ ∃ x s : A, φ s ≠ 0 ∧ φ x ≠ 0 ∧
      f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) x ∧ u = vr e (φ x) - vr e (φ s) := by sorry
