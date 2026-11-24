-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_sum_cons
-- name    : GlobalTheory.VFComp.sum_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:55.115831+00:00
-- url     : https://prove2.me/theorems/44c315e0-ef01-402b-9748-37aa825fb52e
-- title:
--   VFComp: sum cons
-- statement:
--   The VFComp construction uses the sum cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L37-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}

theorem GlobalTheory.VFComp.sum_cons {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (Fin (k + 1) → Fin d) → M) :
    ∑ w : Fin (k + 1) → Fin d, g w = ∑ j : Fin d, ∑ w : Fin k → Fin d, g (Fin.cons j w) := by sorry
