-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_isClosed_siegelOf
-- name    : GlobalTheory.Doubling.isClosed_siegelOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:24.784016+00:00
-- url     : https://prove2.me/theorems/d4973444-fae5-46e5-b00e-dc3cbf1754d4
-- title:
--   Doubling: is Closed siegel Of
-- statement:
--   The Doubling construction uses the is Closed siegel Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L434-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L434-L440

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A)
variable {e mat}
variable [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]

theorem GlobalTheory.Doubling.isClosed_siegelOf [T2Space A] (h : Continuous mat) : IsClosed (siegelOf e mat : Set G) := by sorry
