-- Prove2me | Theorems.Thm_GlobalTheory_FiniteGL_mem_unipRadical
-- name    : GlobalTheory.FiniteGL.mem_unipRadical
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:30.660888+00:00
-- url     : https://prove2.me/theorems/747cf170-b0c3-5699-ac2b-8a27cbf85917
-- title:
--   Finite GL: mem unip Radical
-- statement:
--   The Finite GL construction uses the mem unip Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L63-L64

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

theorem GlobalTheory.FiniteGL.mem_unipRadical {b : Fin N → ℕ} {u : GL (Fin N) k} :
    u ∈ unipRadical k b ↔ ∀ i j, b j ≤ b i → ((u : Matrix (Fin N) (Fin N) k) - 1) i j = 0 := by sorry
