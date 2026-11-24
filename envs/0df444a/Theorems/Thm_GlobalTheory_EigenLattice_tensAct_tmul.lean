-- Prove2me | Theorems.Thm_GlobalTheory_EigenLattice_tensAct_tmul
-- name    : GlobalTheory.EigenLattice.tensAct_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:57.39943+00:00
-- url     : https://prove2.me/theorems/3db8be7f-07b1-40d2-9f9e-73f79ee66e05
-- title:
--   Eigen Lattice: tens Act tmul
-- statement:
--   The Eigen Lattice construction uses the tens Act tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]

theorem GlobalTheory.EigenLattice.tensAct_tmul (ρ : orderC c →+* Module.End O H) (a : orderC c) (x : O) :
    tensAct ρ (a ⊗ₜ x) = x • ρ a := by sorry
