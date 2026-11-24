-- Prove2me | Theorems.Thm_GlobalTheory_RankFibre_X0_mul_invT_parab
-- name    : GlobalTheory.RankFibre.X0_mul_invT_parab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:42.557945+00:00
-- url     : https://prove2.me/theorems/f30f2048-37b3-485f-9b0c-e755e2e63443
-- title:
--   Rank Fibre: X0 mul inv T parab
-- statement:
--   The Rank Fibre construction uses the X0 mul inv T parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreMemInducedSpace.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreMemInducedSpace.lean#L18-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
local notation:70 M:70 " ⬝ₘ " N:71 => HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) M N

theorem GlobalTheory.RankFibre.X0_mul_invT_parab (a b : ℕ) (p : parab k (blocks a b)) :
    X0 k finSumFinEquiv ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val =
      (invT (leviProj k (blocks a b) p false)).val ⬝ₘ X0 k finSumFinEquiv := by sorry
