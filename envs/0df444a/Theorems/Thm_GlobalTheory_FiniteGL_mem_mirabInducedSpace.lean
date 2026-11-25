-- Prove2me | Theorems.Thm_GlobalTheory_FiniteGL_mem_mirabInducedSpace
-- name    : GlobalTheory.FiniteGL.mem_mirabInducedSpace
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:05.119978+00:00
-- url     : https://prove2.me/theorems/229a6786-c775-56db-b7f7-2fee20c1e7a5
-- title:
--   Finite GL: mem mirab Induced Space
-- statement:
--   The Finite GL construction uses the mem mirab Induced Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L143-L147

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

theorem GlobalTheory.FiniteGL.mem_mirabInducedSpace (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) :
    f ∈ MirabInducedSpace n ψ₀ ↔
      ∀ (u : uniSub k n) (x : mirabSub k n), f ((u : mirabSub k n) * x) = genericChar n ψ₀ u * f x := by sorry
