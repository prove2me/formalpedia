-- Prove2me | Theorems.Thm_GlobalTheory_ConeImage_exists_nhds_subset_range
-- name    : GlobalTheory.ConeImage.exists_nhds_subset_range
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:45.685137+00:00
-- url     : https://prove2.me/theorems/95519991-e25b-4bd3-9813-b0cfbec2e638
-- title:
--   Cone Image: exists nhds subset range
-- statement:
--   The Cone Image construction uses the exists nhds subset range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L166-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L166-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage

theorem GlobalTheory.ConeImage.exists_nhds_subset_range {d : ℕ} {A W : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (hd : d ≤ Module.finrank ℂ W)
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hp : p.eval₂ j.toRingHom a = 0)
    (hpq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (hb : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (Φ : W → A →ₐ[ℂ] ℂ) (hΦ : ∀ b, Differentiable ℂ fun w => Φ w b) (w₀ : W)
    (hq : Φ w₀ (j q) ≠ 0) (himm : ∀ ξ, (∀ b, fderiv ℂ (fun w => Φ w b) w₀ ξ = 0) → ξ = 0) :
    ∃ U ∈ 𝓝 (⇑(Φ w₀) : A → ℂ), ∀ φ : A →ₐ[ℂ] ℂ, ⇑φ ∈ U → ∃ w, φ = Φ w := by sorry
