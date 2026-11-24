-- Prove2me | Theorems.Thm_GlobalTheory_Klein_not_red_of_mem
-- name    : GlobalTheory.Klein.not_red_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:33:11.404538+00:00
-- url     : https://prove2.me/theorems/054f7830-aa89-4fbb-b940-79b6cd65547f
-- title:
--   Klein: not red of mem
-- statement:
--   The Klein construction uses the not red of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotRedOfMem.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotRedOfMem.lean#L26-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Klein
open Formalism.L2.Th1.F
open scoped ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.Klein.not_red_of_mem (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {z : ℂ} (h : z ∈ L.lattice) : ¬ Red ι L r z := by sorry
