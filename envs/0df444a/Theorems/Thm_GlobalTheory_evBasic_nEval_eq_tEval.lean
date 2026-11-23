-- Prove2me | Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
-- name    : GlobalTheory.evBasic_nEval_eq_tEval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:22.585111+00:00
-- url     : https://prove2.me/theorems/8f7e03b7-88da-427e-9a3c-3b7b2e57107c
-- title:
--   Global Theory: ev Basic n Eval eq t Eval
-- statement:
--   The Global Theory construction uses the ev Basic n Eval eq t Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBasicNEvalSubCoeffMem.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBasicNEvalSubCoeffMem.lean#L55-L61

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

theorem GlobalTheory.evBasic_nEval_eq_tEval (f : MvPowerSeries ι R₀) (a : ι → S) (N : ℕ)
    (ha : ∀ i, a i ^ N = 0) : nEval f a = tEval N f a := by sorry
