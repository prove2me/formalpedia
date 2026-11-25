-- Prove2me | Theorems.Thm_GlobalTheory_FiniteGL_not_isCuspidal_trivial
-- name    : GlobalTheory.FiniteGL.not_isCuspidal_trivial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:23.528426+00:00
-- url     : https://prove2.me/theorems/970ad5ea-3e39-5e11-94df-465f8df73f8b
-- title:
--   Finite GL: not is Cuspidal trivial
-- statement:
--   The Finite GL construction uses the not is Cuspidal trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L113-L115

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

theorem GlobalTheory.FiniteGL.not_isCuspidal_trivial (hN : 2 ≤ N) : ¬ IsCuspidal (Representation.trivial ℂ (GL (Fin N) k) ℂ) := by sorry
