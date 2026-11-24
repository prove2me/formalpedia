-- Prove2me | Theorems.Thm_GlobalTheory_EigenLattice_inK_apply_map
-- name    : GlobalTheory.EigenLattice.inK_apply_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:46.374404+00:00
-- url     : https://prove2.me/theorems/e3c86cda-09c8-4cf2-9dbf-ec473db5cff1
-- title:
--   Eigen Lattice: in K apply map
-- statement:
--   The Eigen Lattice construction uses the in K apply map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean#L39-L41

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

theorem GlobalTheory.EigenLattice.inK_apply_map (f : Module.End O H) (h : H) :
    inK (O := O) K H (f h) = (f.baseChange K) (inK K H h) := by sorry
