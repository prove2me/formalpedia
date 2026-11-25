-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_regFns_le_fracAlg
-- name    : GlobalTheory.FlagPts.regFns_le_fracAlg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:21.764366+00:00
-- url     : https://prove2.me/theorems/2cc630d6-8470-53e1-80d9-3f031ea57602
-- title:
--   Flag Pts: reg Fns le frac Alg
-- statement:
--   The Flag Pts construction uses the reg Fns le frac Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TruncMatMemSubalgebra.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TruncMatMemSubalgebra.lean#L98-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TruncMatMemSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem GlobalTheory.FlagPts.regFns_le_fracAlg [Fintype ι] (b : Frames k V) : regFns k V ≤ fracAlg b := by sorry
