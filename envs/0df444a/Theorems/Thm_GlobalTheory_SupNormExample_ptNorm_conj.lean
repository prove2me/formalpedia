-- Prove2me | Theorems.Thm_GlobalTheory_SupNormExample_ptNorm_conj
-- name    : GlobalTheory.SupNormExample.ptNorm_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:13.674833+00:00
-- url     : https://prove2.me/theorems/9b63ef81-0a2d-46f4-9530-b9a5456aa9c3
-- title:
--   Sup Norm Example: pt Norm conj
-- statement:
--   The Sup Norm Example construction uses the pt Norm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean#L18-L27

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

theorem GlobalTheory.SupNormExample.ptNorm_conj (σ : K →+* ℂ) (fn : pts (CAt σ) → ι → ℝ)
    (fn' : pts (CAt ((starRingEnd ℂ).comp σ)) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) (z : pts (CAt ((starRingEnd ℂ).comp σ)))
    (hv : evalAt pts mapR f z = conjAt σ (evalAt pts mapR f y)) (hn : ∀ i, |fn' z i| = |fn y i|) :
    ptNorm pts mapR _ fn' e f z = ptNorm pts mapR σ fn e f y := by sorry
