-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_exists_isCompact_of_mul_mem
-- name    : GlobalTheory.FunObj.exists_isCompact_of_mul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:41:51.013212+00:00
-- url     : https://prove2.me/theorems/a65c9679-8daf-4120-a451-911fe3b22087
-- title:
--   Fun Obj: exists is Compact of mul mem
-- statement:
--   The Fun Obj construction uses the exists is Compact of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L75-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

theorem GlobalTheory.FunObj.exists_isCompact_of_mul_mem {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : GL m k) (B : GL n k) :
    ∃ K : Set (Matrix m n k), IsCompact K ∧ ∀ X, A.val * X * B.val ∈ matLat m (stdLat k n) → X ∈ K := by sorry
