-- Prove2me | Theorems.Thm_GlobalTheory_sum_prod_constantCoeff_dmonOf_cols
-- name    : GlobalTheory.sum_prod_constantCoeff_dmonOf_cols
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:30.953098+00:00
-- url     : https://prove2.me/theorems/477d30b5-b896-406f-ba58-3790d247b629
-- title:
--   Global Theory: sum prod constant Coeff dmon Of cols
-- statement:
--   The Global Theory construction uses the sum prod constant Coeff dmon Of cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdConstantCoeffDmonOfCols.lean#L53-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdConstantCoeffDmonOfCols.lean#L53-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open SymbolCols

theorem GlobalTheory.sum_prod_constantCoeff_dmonOf_cols :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (u : ι → Fin d → k) (lam : Fin n → ι → Fin d → k) (α : ι → k) (al : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) k) (g E : Fin n → PS k 1 d), P.IsHomogeneous al.degree → (∀ b l l', al (l, b) ≠ 0 → (∃ mo ∈ P.support, mo (l', b) ≠ 0) → ∑ i, lam b l i * u l' i = if l = l' then α l else 0) → (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (g b) = coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) = P.coeff al * ∏ b, ((∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b)) := by sorry
