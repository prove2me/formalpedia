-- Prove2me | Theorems.Thm_GlobalTheory_LowerOps_ext_of_eigLat
-- name    : GlobalTheory.LowerOps.ext_of_eigLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:16:48.368715+00:00
-- url     : https://prove2.me/theorems/8294c543-44ba-4099-9364-75d840df1188
-- title:
--   Lower Ops: ext of eig Lat
-- statement:
--   The Lower Ops construction uses the ext of eig Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L33-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L33-L56

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

theorem GlobalTheory.LowerOps.ext_of_eigLat [IsDomain O] [IsFractionRing O K] (ρ : orderC c →+* Module.End O H) (D : O) (hD : D ≠ 0)
    (hsum : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ) (S T : Module.End K (K ⊗[O] H))
    (hST : ∀ σ : E →+* K, ∀ y ∈ eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y)) : S = T := by sorry
