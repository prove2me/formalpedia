-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_mul
-- name    : GlobalTheory.Reg.Transfer.chval_fin_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:34.253991+00:00
-- url     : https://prove2.me/theorems/1bfea609-8c6a-4fa7-b620-fb88d554cee9
-- title:
--   Transfer: chval fin mul
-- statement:
--   The Transfer construction uses the chval fin mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L178-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L178-L187

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

theorem GlobalTheory.Reg.Transfer.chval_fin_mul (φ : A →+* V) (e : ℕ) {f1 f2 : FractionRing A} {u1 u2 : ℝ}
    (h1 : ChV φ e f1 (u1 : EReal)) (h2 : ChV φ e f2 (u2 : EReal)) :
    ChV φ e (f1 * f2) ((u1 + u2 : ℝ) : EReal) := by sorry
