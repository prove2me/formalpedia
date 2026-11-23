-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_fac
-- name    : GlobalTheory.SW.MinkowskiProductBounds.fac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:52.266391+00:00
-- url     : https://prove2.me/theorems/b4a5ef4a-a5b2-44b1-84c7-e120f16686c8
-- title:
--   Minkowski Product Bounds: fac
-- statement:
--   The Minkowski Product Bounds construction uses the fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L165-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L165-L178

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

theorem GlobalTheory.SW.MinkowskiProductBounds.fac {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) :
    ∃ B : Matrix (Fin m) (Fin m) ℂ, H = B * Bᴴ ∧ (∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* B)) (WithLp.toLp 2 (x ᵥ* B))) ∧
      ∀ x : Fin m → ℂ, (x ⬝ᵥ H *ᵥ star x).re = ‖WithLp.toLp 2 (x ᵥ* B)‖ ^ 2 := by sorry
