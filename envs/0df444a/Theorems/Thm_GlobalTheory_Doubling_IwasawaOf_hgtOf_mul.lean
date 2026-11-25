-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IwasawaOf_hgtOf_mul
-- name    : GlobalTheory.Doubling.IwasawaOf.hgtOf_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:00.285698+00:00
-- url     : https://prove2.me/theorems/59ecb14f-c249-49f0-a52f-74dee99eec59
-- title:
--   Iwasawa Of: hgt Of mul
-- statement:
--   The Iwasawa Of construction uses the hgt Of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L487-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L487-L488

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

theorem GlobalTheory.Doubling.IwasawaOf.hgtOf_mul (h : IwasawaOf e mat ν K) (p : siegelOf e mat) {k : G} (hk : k ∈ K) :
    hgtOf e mat ν K (p * k) = ν (aOf e mat p) := by sorry
