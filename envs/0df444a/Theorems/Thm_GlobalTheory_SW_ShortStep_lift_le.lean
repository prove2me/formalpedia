-- Prove2me | Theorems.Thm_GlobalTheory_SW_ShortStep_lift_le
-- name    : GlobalTheory.SW.ShortStep.lift_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:43.868241+00:00
-- url     : https://prove2.me/theorems/9c8c1997-f9cf-489f-bde7-14dc07834229
-- title:
--   Short Step: lift le
-- statement:
--   The Short Step construction uses the lift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L385-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L385-L404

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem GlobalTheory.SW.ShortStep.lift_le {n m : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (V : Matrix (Fin 1) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin m) (Fin 1) ℂ)
    (t : Fin m → ℂ) (α : ℂ) {C M : ℝ} (hM : 1 ≤ M) (h1 : (V 0 ⬝ᵥ H *ᵥ star (V 0)).re ≤ C)
    (h2 : (t ⬝ᵥ ((B - L * V) * H * (B - L * V)ᴴ) *ᵥ star t).re ≤ C)
    (h3 : ‖α + (t ᵥ* L) 0‖ ≤ M) :
    ((t ᵥ* B + α • V 0) ⬝ᵥ H *ᵥ star (t ᵥ* B + α • V 0)).re ≤ (2 * (M * √C)) ^ 2 := by sorry
