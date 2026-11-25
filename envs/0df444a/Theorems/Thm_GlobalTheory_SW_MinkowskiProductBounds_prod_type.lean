-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_prod_type
-- name    : GlobalTheory.SW.MinkowskiProductBounds.prod_type
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:29.90982+00:00
-- url     : https://prove2.me/theorems/08021251-e1ed-4927-b003-defe74e55720
-- title:
--   Minkowski Product Bounds: prod type
-- statement:
--   The Minkowski Product Bounds construction uses the prod type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L61-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L61-L78

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

theorem GlobalTheory.SW.MinkowskiProductBounds.prod_type {M : Type} [CommMonoid M] (h : IsType Ψ) (f : (E →+* ℂ) → M) :
    ∏ σ, f σ = ∏ τ : Ψ, (f τ.1 * f (ComplexEmbedding.conjugate τ.1)) := by sorry
