-- Prove2me | Theorems.Thm_GlobalTheory_EigenLattice_exists_ne_mem
-- name    : GlobalTheory.EigenLattice.exists_ne_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:19.888578+00:00
-- url     : https://prove2.me/theorems/17462a6c-5b39-4a0a-b9b1-8c036788c6e3
-- title:
--   Eigen Lattice: exists ne mem
-- statement:
--   The Eigen Lattice construction uses the exists ne mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralSecond.lean#L20-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralSecond.lean#L20-L35

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

theorem GlobalTheory.EigenLattice.exists_ne_mem (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (h1 : Module.finrank K (eigK ρ σ) = 1) :
    ∃ g : H, g ≠ 0 ∧ g ∈ eigLat ρ σ := by sorry
