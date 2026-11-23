-- Prove2me | Theorems.Thm_GlobalTheory_Div_eigen_line_bilinear_eq_smul_of_line
-- name    : GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:00.524321+00:00
-- url     : https://prove2.me/theorems/a00649c0-2f29-4975-849e-221cd7764f82
-- title:
--   eigen line bilinear: eq smul of line
-- statement:
--   The eigen line bilinear construction uses the eq smul of line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L27-L31

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

theorem GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line {ρ : orderC c →+* Module.End O H} {τ : E →+* K} (hline : Module.finrank K (eigK ρ τ) = 1)
    {v : K ⊗[O] H} (hv : v ∈ eigK ρ τ) (hv0 : v ≠ 0) {x : K ⊗[O] H} (hx : x ∈ eigK ρ τ) : ∃ a : K, x = a • v := by sorry
