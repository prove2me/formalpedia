-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_gramLB_shift
-- name    : GlobalTheory.ClassFin.gramLB_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:25.522695+00:00
-- url     : https://prove2.me/theorems/49b4049c-7759-499c-99dc-b9f953e29f09
-- title:
--   Class Fin: gram LB shift
-- statement:
--   The Class Fin construction uses the gram LB shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/GramLeadingMinorLowerBoundIntegral.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/GramLeadingMinorLowerBoundIntegral.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin

theorem GlobalTheory.ClassFin.gramLB_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by sorry
