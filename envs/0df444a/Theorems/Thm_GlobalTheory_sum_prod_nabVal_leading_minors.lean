-- Prove2me | Theorems.Thm_GlobalTheory_sum_prod_nabVal_leading_minors
-- name    : GlobalTheory.sum_prod_nabVal_leading_minors
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:59.320317+00:00
-- url     : https://prove2.me/theorems/d90a8ba9-1822-4d4b-9ab9-df192b84a147
-- title:
--   Global Theory: sum prod nab Val leading minors
-- statement:
--   The Global Theory construction uses the sum prod nab Val leading minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L67-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L67-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors
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
open CrudeValue SymbolCols

theorem GlobalTheory.sum_prod_nabVal_leading_minors : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by sorry
