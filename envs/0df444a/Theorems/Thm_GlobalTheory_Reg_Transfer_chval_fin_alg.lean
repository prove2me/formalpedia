-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_alg
-- name    : GlobalTheory.Reg.Transfer.chval_fin_alg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:18:40.11168+00:00
-- url     : https://prove2.me/theorems/a33ab5e3-07e5-4aba-8149-e853180c4f4f
-- title:
--   Transfer: chval fin alg
-- statement:
--   The Transfer construction uses the chval fin alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L217-L222

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

theorem GlobalTheory.Reg.Transfer.chval_fin_alg (φ : A →+* V) (e : ℕ) (a : A) (ha : φ a ≠ 0) :
    ChV φ e (algebraMap A (FractionRing A) a) ((vr e (φ a) : ℝ) : EReal) := by sorry
