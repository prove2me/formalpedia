-- Prove2me | Theorems.Thm_GlobalTheory_constantCoeff_dmonOf_prod_linear
-- name    : GlobalTheory.constantCoeff_dmonOf_prod_linear
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:36.614095+00:00
-- url     : https://prove2.me/theorems/bbb54c67-32f0-4ee6-8301-b8a75bc2fe82
-- title:
--   Global Theory: constant Coeff dmon Of prod linear
-- statement:
--   The Global Theory construction uses the constant Coeff dmon Of prod linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L245-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L245-L268

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open SymbolOne

theorem GlobalTheory.constantCoeff_dmonOf_prod_linear :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (u lam : ι → Fin d → k) (α : ι → k) (al m : ι →₀ ℕ) (E : PS k 1 d), (∀ l l', al l ≠ 0 → m l' ≠ 0 → ∑ i, lam l i * u l' i = if l = l' then α l else 0) → m.degree ≤ al.degree → constantCoeff (DmonOf (G.mapF φ) u m ((∏ l, (∑ i, C (lam l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al l) * E)) = if m = al then (∏ l, ((al l).factorial : k) * α l ^ al l) * constantCoeff E else 0 := by sorry
