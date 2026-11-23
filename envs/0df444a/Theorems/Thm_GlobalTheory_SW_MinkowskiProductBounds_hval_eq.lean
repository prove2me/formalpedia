-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_hval_eq
-- name    : GlobalTheory.SW.MinkowskiProductBounds.hval_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:50.819799+00:00
-- url     : https://prove2.me/theorems/c8643ceb-c2f5-46a5-bdde-bd33bc375891
-- title:
--   Minkowski Product Bounds: hval eq
-- statement:
--   The Minkowski Product Bounds construction uses the hval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L180-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L180-L181

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

theorem GlobalTheory.SW.MinkowskiProductBounds.hval_eq {m : ℕ} (H : CM Ψ m m) (τ : Ψ) (v : Fin m → E) :
    hval Ψ H τ v = ((fun a => τ.1 (v a)) ⬝ᵥ H τ *ᵥ star fun a => τ.1 (v a)).re := by sorry
