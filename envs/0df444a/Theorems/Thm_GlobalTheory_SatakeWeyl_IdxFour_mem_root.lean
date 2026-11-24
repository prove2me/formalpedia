-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_mem_root
-- name    : GlobalTheory.SatakeWeyl.IdxFour.mem_root
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:56.8528+00:00
-- url     : https://prove2.me/theorems/08c12df3-6fb5-421b-9121-155ec7e545ee
-- title:
--   Idx Four: mem root
-- statement:
--   The Idx Four construction uses the mem root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean#L67-L72

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

theorem GlobalTheory.SatakeWeyl.IdxFour.mem_root {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) : g ∈ rootU σ ![0, 0, 1, 1] := by sorry
