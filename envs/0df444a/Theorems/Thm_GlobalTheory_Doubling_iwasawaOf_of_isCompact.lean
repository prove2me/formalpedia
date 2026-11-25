-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_iwasawaOf_of_isCompact
-- name    : GlobalTheory.Doubling.iwasawaOf_of_isCompact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:10:36.543251+00:00
-- url     : https://prove2.me/theorems/e3d79a63-5d6f-5c90-bc55-f8df3ca172ee
-- title:
--   Doubling: iwasawa Of of is Compact
-- statement:
--   The Doubling construction uses the iwasawa Of of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L494-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L494-L496

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
omit [IsTopologicalGroup G]

theorem GlobalTheory.Doubling.iwasawaOf_of_isCompact (hm : Continuous mat) (hν : Continuous ν) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : siegelOf e mat, ∃ k ∈ K, g = p * k) : IwasawaOf e mat ν K := by sorry
