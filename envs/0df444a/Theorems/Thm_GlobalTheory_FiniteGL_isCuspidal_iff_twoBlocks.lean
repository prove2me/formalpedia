-- Prove2me | Theorems.Thm_GlobalTheory_FiniteGL_isCuspidal_iff_twoBlocks
-- name    : GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:43.858803+00:00
-- url     : https://prove2.me/theorems/f9c19609-477b-41d2-98da-36053214c518
-- title:
--   Finite GL: is Cuspidal iff two Blocks
-- statement:
--   The Finite GL construction uses the is Cuspidal iff two Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L72-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L72-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
variable (k : Type) [Field k] {N : ℕ}
variable {k}
variable (k)
variable {k}

theorem GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal ρ ↔ ∀ a : ℕ, 0 < a → a < N →
      ∀ v : V, (∀ u ∈ unipRadical k (twoBlocks N a), ρ u v = v) → v = 0 := by sorry
