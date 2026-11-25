-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_exists_convergence
-- name    : GlobalTheory.AnArc.exists_convergence
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:01.832249+00:00
-- url     : https://prove2.me/theorems/a9ddc22d-ac69-50ae-bf2f-b630e5f59547
-- title:
--   An Arc: exists convergence
-- statement:
--   The An Arc construction uses the exists convergence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L403-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L403-L420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.exists_convergence : ∃ T₀ : ℝ, ∀ (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ), th ∈ A.Theta j α →
    (∀ p : ℂ × A.V, T₀ < p.1.im → ∃ t ∈ 𝓝 p, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ q ∈ t,
      ‖A.term j α th μ q.2 * eTwoPi (q.1 * A.exponent j α μ)‖ ≤ u μ) ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v, Summable fun μ => ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖) ∧
    HasSumLocallyUniformlyOn (fun μ (p : ℂ × A.V) => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ))
      (fun p => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} ∧
    DifferentiableOn ℂ (fun p : ℂ × A.V => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v,
      HasSum (fun n : ℤ => (A.FSum j α th v).coeff n * eTwoPi w ^ n) (A.Sum j α th w v)) ∧
    (∀ n : ℤ, Differentiable ℂ fun v => (A.FSum j α th v).coeff n) ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v v₀,
      HasSum (fun n : ℤ => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v v₀ * eTwoPi w ^ n)
        (fderiv ℂ (A.Sum j α th w) v v₀)) := by sorry
