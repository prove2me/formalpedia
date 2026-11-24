-- Prove2me | Theorems.Thm_GlobalTheory_Div_eigen_line_bilinear_lower_apply
-- name    : GlobalTheory.Div.eigen_line_bilinear.lower_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:42.255796+00:00
-- url     : https://prove2.me/theorems/0b5822c2-b954-43b0-92ef-ebe89883b692
-- title:
--   eigen line bilinear: lower apply
-- statement:
--   The eigen line bilinear construction uses the lower apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L33-L48

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

theorem GlobalTheory.Div.eigen_line_bilinear.lower_apply {ρ : orderC c →+* Module.End O H} {τ : E →+* K} {e f : H} {N : Module.End K (K ⊗[O] H)}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (hline : Module.finrank K (eigK ρ τ) = 1)
    (he : inK (O := O) K H e ∈ eigK ρ τ) (he0 : inK (O := O) K H e ≠ 0) (hN : IsLower ρ τ e f N) (x : K ⊗[O] H) :
    ∃ a : K, N x = a • inK (O := O) K H f := by sorry
