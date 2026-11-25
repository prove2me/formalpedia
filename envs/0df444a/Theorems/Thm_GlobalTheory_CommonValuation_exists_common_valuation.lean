-- Prove2me | Theorems.Thm_GlobalTheory_CommonValuation_exists_common_valuation
-- name    : GlobalTheory.CommonValuation.exists_common_valuation
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:46.929598+00:00
-- url     : https://prove2.me/theorems/a490ea93-8825-4016-9d50-5bc02058c0f2
-- title:
--   Common Valuation: exists common valuation
-- statement:
--   The Common Valuation construction uses the exists common valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationIndexValuationCompat.lean#L99-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationIndexValuationCompat.lean#L99-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation

theorem GlobalTheory.CommonValuation.exists_common_valuation : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (em : k →+* K) (e : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → 0 < e → (∀ z : k, (IsDiscreteValuationRing.maximalIdeal V).valuation K (em z) = 𝔭.valuation k z ^ e) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (f : V →+* W) (g : K →+* L) (em' : k' →+* L) (e' d : ℕ), (∀ z : V, algebraMap W L (f z) = g (algebraMap V K z)) ∧ em'.comp i = g.comp em ∧ 0 < e' ∧ e' * ε = d * e ∧ (∀ z : k', (IsDiscreteValuationRing.maximalIdeal W).valuation L (em' z) = 𝔓.valuation k' z ^ e') ∧ ∀ y : K, (IsDiscreteValuationRing.maximalIdeal W).valuation L (g y) = (IsDiscreteValuationRing.maximalIdeal V).valuation K y ^ d := by sorry
