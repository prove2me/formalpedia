-- Prove2me | Theorems.Thm_GlobalTheory_SupNormExample_bddAt_of_fnorm_zero
-- name    : GlobalTheory.SupNormExample.bddAt_of_fnorm_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:02.451484+00:00
-- url     : https://prove2.me/theorems/10010111-75fa-4378-b16e-a59f85ebd615
-- title:
--   Sup Norm Example: bdd At of fnorm zero
-- statement:
--   The Sup Norm Example construction uses the bdd At of fnorm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean#L29-L36

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

theorem GlobalTheory.SupNormExample.bddAt_of_fnorm_zero (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    BddAt pts mapR σ (fun _ _ => 0) e f ∧ supAt pts mapR σ (fun _ _ => 0) e f = 0 := by sorry
