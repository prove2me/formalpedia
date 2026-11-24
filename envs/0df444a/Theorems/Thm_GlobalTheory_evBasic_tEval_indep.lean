-- Prove2me | Theorems.Thm_GlobalTheory_evBasic_tEval_indep
-- name    : GlobalTheory.evBasic_tEval_indep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:19:57.412567+00:00
-- url     : https://prove2.me/theorems/cd0da74f-394f-490d-a982-cf8360b890af
-- title:
--   Global Theory: ev Basic t Eval indep
-- statement:
--   The Global Theory construction uses the ev Basic t Eval indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBasicNEvalSubCoeffMem.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBasicNEvalSubCoeffMem.lean#L49-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]

theorem GlobalTheory.evBasic_tEval_indep {N N' : ℕ} (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) (ha' : ∀ i, a i ^ N' = 0) : tEval N f a = tEval N' f a := by sorry
