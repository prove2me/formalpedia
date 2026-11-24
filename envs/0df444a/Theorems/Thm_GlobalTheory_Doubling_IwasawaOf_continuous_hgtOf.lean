-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IwasawaOf_continuous_hgtOf
-- name    : GlobalTheory.Doubling.IwasawaOf.continuous_hgtOf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:07.552713+00:00
-- url     : https://prove2.me/theorems/88ed44e7-f7a9-4c83-911c-cd6a95e964d6
-- title:
--   Iwasawa Of: continuous hgt Of
-- statement:
--   The Iwasawa Of construction uses the continuous hgt Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L498-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L498-L500

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
open scoped NNReal
open MeasureTheory
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)
variable {e mat ν K}
variable [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.Doubling.IwasawaOf.continuous_hgtOf (h : IwasawaOf e mat ν K) (hm : Continuous mat) (hν : Continuous ν)
    (hK : IsCompact (K : Set G)) : Continuous (hgtOf e mat ν K) := by sorry
