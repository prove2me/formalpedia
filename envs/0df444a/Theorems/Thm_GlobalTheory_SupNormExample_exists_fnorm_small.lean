-- Prove2me | Theorems.Thm_GlobalTheory_SupNormExample_exists_fnorm_small
-- name    : GlobalTheory.SupNormExample.exists_fnorm_small
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:25.987375+00:00
-- url     : https://prove2.me/theorems/3111ad68-caae-4e2f-b329-f20b8672ee7f
-- title:
--   Sup Norm Example: exists fnorm small
-- statement:
--   The Sup Norm Example construction uses the exists fnorm small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean#L38-L57

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SupNormExample
open Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

theorem GlobalTheory.SupNormExample.exists_fnorm_small (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    ∃ fnorm : pts (CAt σ) → ι → ℝ, (∀ y j, 0 < fnorm y j) ∧ BddAt pts mapR σ fnorm e f ∧
      supAt pts mapR σ fnorm e f ≤ 1 := by sorry
