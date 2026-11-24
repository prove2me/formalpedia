-- Prove2me | Theorems.Thm_GlobalTheory_DetBound_gens_mem_linearIndependent
-- name    : GlobalTheory.DetBound.gens_mem_linearIndependent
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:59:33.335474+00:00
-- url     : https://prove2.me/theorems/7844044b-f768-46fb-86ce-a5714842a930
-- title:
--   Det Bound: gens mem linear Independent
-- statement:
--   The Det Bound construction uses the gens mem linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L121-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L121-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
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
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem GlobalTheory.DetBound.gens_mem_linearIndependent {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) : (∀ i, e i ∈ Fil) ∧ LinearIndependent O e := by sorry
