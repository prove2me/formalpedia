-- Prove2me | Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
-- name    : GlobalTheory.FiniteGL.restrictMirab_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:09.857663+00:00
-- url     : https://prove2.me/theorems/c516a78a-3f88-4bab-8afe-bbdea8e8f7d7
-- title:
--   Finite GL: restrict Mirab apply
-- statement:
--   The Finite GL construction uses the restrict Mirab apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L159-L161

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

theorem GlobalTheory.FiniteGL.restrictMirab_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (n + 1)) k) V) (h : mirabSub k n) :
    restrictMirab n ρ h = ρ (h : GL (Fin (n + 1)) k) := by sorry

attribute [defeq] GlobalTheory.FiniteGL.restrictMirab_apply
