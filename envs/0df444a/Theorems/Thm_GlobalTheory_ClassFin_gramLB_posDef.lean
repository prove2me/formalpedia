-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_gramLB_posDef
-- name    : GlobalTheory.ClassFin.gramLB_posDef
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:05.727628+00:00
-- url     : https://prove2.me/theorems/be632d42-9530-4e8f-991f-5d4f3f1a6f60
-- title:
--   Class Fin: gram LB pos Def
-- statement:
--   The Class Fin construction uses the gram LB pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/GramLeadingMinorLowerBoundIntegral.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/GramLeadingMinorLowerBoundIntegral.lean#L90-L94

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

theorem GlobalTheory.ClassFin.gramLB_posDef {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by sorry
