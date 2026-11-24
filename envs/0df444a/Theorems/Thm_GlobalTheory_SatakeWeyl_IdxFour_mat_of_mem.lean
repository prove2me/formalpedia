-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_mat_of_mem
-- name    : GlobalTheory.SatakeWeyl.IdxFour.mat_of_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:12.539371+00:00
-- url     : https://prove2.me/theorems/1b73b63a-9501-44ef-98df-6106b319d028
-- title:
--   Idx Four: mat of mem
-- statement:
--   The Idx Four construction uses the mat of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean#L34-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean#L34-L65

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.IdxFour.mat_of_mem (hσ : ∀ x, σ (σ x) = x) {g : GU σ 4} (hg : g ∈ rootU σ ![0, 0, 1, 1]) :
    mat g = rootMat σ (mat g 0 1) := by sorry
