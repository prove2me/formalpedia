-- Prove2me | Theorems.Thm_GlobalTheory_FiniteGL_genericChar_apply
-- name    : GlobalTheory.FiniteGL.genericChar_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:39.036407+00:00
-- url     : https://prove2.me/theorems/e5134053-1fdb-4f9a-b5ac-5d5e5bb97970
-- title:
--   Finite GL: generic Char apply
-- statement:
--   The Finite GL construction uses the generic Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L130-L132

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
variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem GlobalTheory.FiniteGL.genericChar_apply (ψ₀ : AddChar k ℂ) (u : uniSub k n) :
    genericChar n ψ₀ u =
      ψ₀ (supd (((u : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) := by sorry
