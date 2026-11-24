-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_isIntegral_and_rational
-- name    : GlobalTheory.ThetaRational.isIntegral_and_rational
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:07:39.338648+00:00
-- url     : https://prove2.me/theorems/4c105c81-2be8-41e8-87c4-d17ebed15afc
-- title:
--   Theta Rational: is Integral and rational
-- statement:
--   The Theta Rational construction uses the is Integral and rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L389-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L389-L540

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]

theorem GlobalTheory.ThetaRational.isIntegral_and_rational
    (hnoeth : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a))
    (hrat : (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map (MvPolynomial.eval z.1)).eval z.2))
    {u : ι → E → ℂ} {h : E → ℂ} (hu : ∀ c, Differentiable ℂ (u c)) (hh : Differentiable ℂ h)
    (hcl : ∀ y : ι → ℂ, (∀ F : MvPolynomial ι ℂ, (∀ e, MvPolynomial.eval (fun c => u c e) F = 0) →
      MvPolynomial.eval y F = 0) → ∃ e, y = fun c => u c e)
    {c₀ : ι} (hc₀ : u c₀ ≠ 0)
    (hdesc : ∀ e, (fun c => u c e) ≠ 0 → ∃ G : (ι → ℂ) → ℂ, AnalyticAt ℂ G (fun c => u c e) ∧
      ∀ᶠ y in 𝓝 (fun c => u c e), ∀ x, (fun c => u c x) = y → h x = G y)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C) (hgr : ∀ e, ‖h e‖ ≤ C * ‖fun c => u c e‖ ^ m) :
    IsIntegral (Algebra.adjoin ℂ (Set.range u)) h ∧
      ∃ a ∈ Algebra.adjoin ℂ (Set.range u), ∃ b ∈ Algebra.adjoin ℂ (Set.range u),
        b ≠ 0 ∧ b * h = a := by sorry
