-- Prove2me | Theorems.Thm_GlobalTheory_Div_eigen_line_bilinear_bilin_zero_of_eig
-- name    : GlobalTheory.Div.eigen_line_bilinear.bilin_zero_of_eig
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:34.509815+00:00
-- url     : https://prove2.me/theorems/3fb034f9-ab8d-4ff8-ac54-e48820b9cde6
-- title:
--   eigen line bilinear: bilin zero of eig
-- statement:
--   The eigen line bilinear construction uses the bilin zero of eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L50-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
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
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.eigen_line_bilinear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.Div.eigen_line_bilinear.bilin_zero_of_eig {ρ : orderC c →+* Module.End O H}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (S : LinearMap.BilinForm K (K ⊗[O] H))
    (h : ∀ σ σ' : E →+* K, ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', S x y = 0) (x y : K ⊗[O] H) : S x y = 0 := by sorry
