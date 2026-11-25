-- Prove2me | Theorems.Thm_GlobalTheory_canonGauge_independence_harmonic
-- name    : GlobalTheory.canonGauge_independence_harmonic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:32:09.912394+00:00
-- url     : https://prove2.me/theorems/48bb6c0d-1a2b-4c31-a481-afc0b50ab559
-- title:
--   Global Theory: canon Gauge independence harmonic
-- statement:
--   The Global Theory construction uses the canon Gauge independence harmonic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeIndependenceHarmonic.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeIndependenceHarmonic.lean#L54-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeSubIsBiadd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
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

theorem GlobalTheory.canonGauge_independence_harmonic :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), (∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b) (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0) → ∀ (w0 : O) (mm : ℕ) (f : Fin n → PS k 1 d), ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) = ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h' w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) := by sorry
