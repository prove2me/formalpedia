-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:22.303439+00:00
-- url     : https://prove2.me/theorems/3929a7aa-e51d-49fa-85c6-06019e654d73
-- title:
--   Omega Factorization: wirt Word cons
-- statement:
--   The Omega Factorization construction uses the wirt Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L121-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons {Φ : Type} [Fintype Φ] (w : Φ × Bool) (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) :
    wirtWord (w :: ws) g = wirt w.1 w.2 (wirtWord ws g) := by sorry
