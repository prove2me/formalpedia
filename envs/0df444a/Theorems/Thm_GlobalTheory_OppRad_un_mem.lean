-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_un_mem
-- name    : GlobalTheory.OppRad.un_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:47.348622+00:00
-- url     : https://prove2.me/theorems/ba605452-c538-4ce1-b68e-22a6fe49923d
-- title:
--   Opp Rad: un mem
-- statement:
--   The Opp Rad construction uses the un mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L38-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]

theorem GlobalTheory.OppRad.un_mem {p q x : R} (h : x * x = 0) (h1 : p * x = x) (h2 : x * q = x) : un x h ∈ U p q := by sorry
