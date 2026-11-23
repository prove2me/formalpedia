-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Placing_Moves_symm
-- name    : GlobalTheory.SmGL.Placing.Moves.symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:56.057703+00:00
-- url     : https://prove2.me/theorems/aa0fb235-133e-4e94-96f9-7922dfe212c0
-- title:
--   Moves: symm
-- statement:
--   The Moves construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean#L125-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.SmGL.Placing.Moves.symm {ι : Type} {e e' : ι ≃ n} {w : GL n R} (h : Moves e e' w) : Moves e' e w⁻¹ := by sorry
