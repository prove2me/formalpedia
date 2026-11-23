-- Prove2me | Theorems.Thm_GlobalTheory_evBasic_exists_pow
-- name    : GlobalTheory.evBasic_exists_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:20.405995+00:00
-- url     : https://prove2.me/theorems/096f2e93-ce99-4a13-a7fc-8f7635337907
-- title:
--   Global Theory: ev Basic exists pow
-- statement:
--   The Global Theory construction uses the ev Basic exists pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBasicNEvalSubCoeffMem.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBasicNEvalSubCoeffMem.lean#L65-L70

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
omit [DecidableEq ι]

theorem GlobalTheory.evBasic_exists_pow (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, a i ^ N = 0 := by sorry
