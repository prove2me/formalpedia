-- Prove2me | Theorems.Thm_GlobalTheory_BCT_SuppFin_isOpen_vle
-- name    : GlobalTheory.BCT.SuppFin.isOpen_vle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:41.222089+00:00
-- url     : https://prove2.me/theorems/7b8ccb9a-b3e6-48e7-b459-d08fe23cb7af
-- title:
--   Supp Fin: is Open vle
-- statement:
--   The Supp Fin construction uses the is Open vle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompact.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompact.lean#L10-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
noncomputable section
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.BCT.SuppFin.isOpen_vle (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by sorry
