-- Prove2me | Theorems.Thm_GlobalTheory_EigenLattice_tensAct_eig
-- name    : GlobalTheory.EigenLattice.tensAct_eig
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:53:00.95557+00:00
-- url     : https://prove2.me/theorems/80096f93-4cf1-42ab-85e9-3c48f19875b7
-- title:
--   Eigen Lattice: tens Act eig
-- statement:
--   The Eigen Lattice construction uses the tens Act eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean#L25-L37

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

theorem GlobalTheory.EigenLattice.tensAct_eig (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (v : K ⊗[O] H)
    (hv : v ∈ eigK ρ σ) (t : orderC c ⊗[ℤ] O) :
    ((tensAct ρ t).baseChange K) v = coordAt O c σ t • v := by sorry
