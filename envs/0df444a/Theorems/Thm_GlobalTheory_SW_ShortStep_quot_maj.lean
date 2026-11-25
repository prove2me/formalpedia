-- Prove2me | Theorems.Thm_GlobalTheory_SW_ShortStep_quot_maj
-- name    : GlobalTheory.SW.ShortStep.quot_maj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:29.244831+00:00
-- url     : https://prove2.me/theorems/8cd06cc4-df58-47b2-9bff-9ea4eb3495ba
-- title:
--   Short Step: quot maj
-- statement:
--   The Short Step construction uses the quot maj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L15-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L15-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds

theorem GlobalTheory.SW.ShortStep.quot_maj {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G H : Matrix n n ℂ} {V w : Matrix (Fin 1) n ℂ} {B : Matrix m n ℂ} {S : Matrix n m ℂ}
    (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hH : H.PosDef) (hm : H * G⁻¹ * H = G)
    (hw : V * G * wᴴ = 1) (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) (hd : (B * G * Bᴴ).det ≠ 0) :
    ∃ L : Matrix m (Fin 1) ℂ, ((B - L * V) * H * (B - L * V)ᴴ).PosDef ∧
      (B - L * V) * H * (B - L * V)ᴴ * (B * G * Bᴴ)⁻¹ * ((B - L * V) * H * (B - L * V)ᴴ) =
        B * G * Bᴴ := by sorry
