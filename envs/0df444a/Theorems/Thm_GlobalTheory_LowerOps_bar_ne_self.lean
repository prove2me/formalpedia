-- Prove2me | Theorems.Thm_GlobalTheory_LowerOps_bar_ne_self
-- name    : GlobalTheory.LowerOps.bar_ne_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:18:51.953796+00:00
-- url     : https://prove2.me/theorems/a60efd03-318b-4883-adfe-e25a26767e94
-- title:
--   Lower Ops: bar ne self
-- statement:
--   The Lower Ops construction uses the bar ne self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L24-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.LowerOps.bar_ne_self (σ : E →+* K) : bar σ ≠ σ := by sorry
