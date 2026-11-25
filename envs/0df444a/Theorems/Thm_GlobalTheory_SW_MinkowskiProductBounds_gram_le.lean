-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_gram_le
-- name    : GlobalTheory.SW.MinkowskiProductBounds.gram_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:34.930696+00:00
-- url     : https://prove2.me/theorems/061fcbb3-8bfc-4e97-81cd-82e577e7d4e9
-- title:
--   Minkowski Product Bounds: gram le
-- statement:
--   The Minkowski Product Bounds construction uses the gram le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L253-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L253-L268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem GlobalTheory.SW.MinkowskiProductBounds.gram_le {m : ℕ} {H G : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) (hG : Gᴴ = G)
    (h0 : G.det ≠ 0) (hm : H * G⁻¹ * H = G) (x y : Fin m → ℂ) {C : ℝ}
    (hx : (x ⬝ᵥ H *ᵥ star x).re ≤ C) (hy : (y ⬝ᵥ H *ᵥ star y).re ≤ C) :
    ‖x ⬝ᵥ G *ᵥ star y‖ ≤ C := by sorry
