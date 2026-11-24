-- Prove2me | Theorems.Thm_GlobalTheory_EigenLattice_finrank_le
-- name    : GlobalTheory.EigenLattice.finrank_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:59.51408+00:00
-- url     : https://prove2.me/theorems/b14d356a-77db-49bc-8495-816a3f1e7f7c
-- title:
--   Eigen Lattice: finrank le
-- statement:
--   The Eigen Lattice construction uses the finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralSecond.lean#L37-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralSecond.lean#L37-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond
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
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.EigenLattice.finrank_le [Module.Free O H] [Module.Finite O H] (ρ : orderC c →+* Module.End O H) (σ : E →+* K)
    (h1 : Module.finrank K (eigK ρ σ) = 1) : Module.finrank O (eigLat ρ σ) ≤ 1 := by sorry
