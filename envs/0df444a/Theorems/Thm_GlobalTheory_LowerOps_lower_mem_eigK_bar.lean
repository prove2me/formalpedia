-- Prove2me | Theorems.Thm_GlobalTheory_LowerOps_lower_mem_eigK_bar
-- name    : GlobalTheory.LowerOps.lower_mem_eigK_bar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:18:51.50282+00:00
-- url     : https://prove2.me/theorems/81ae6920-ce77-49db-8d1b-735717dcd1d8
-- title:
--   Lower Ops: lower mem eig K bar
-- statement:
--   The Lower Ops construction uses the lower mem eig K bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L58-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
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
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.LowerOps.lower_mem_eigK_bar {I : Type} {φ : I → E →+* K} {ρ : orderC c →+* Module.End O H} {e f : I → H}
    (hG : IsGens φ ρ e f) {i : I} {N : Module.End K (K ⊗[O] H)} (hN : IsLower ρ (φ i) (e i) (f i) N) {y : H}
    (hy : y ∈ eigLat (K := K) ρ (φ i)) : N (inK K H y) ∈ eigK ρ (bar (φ i)) := by sorry
