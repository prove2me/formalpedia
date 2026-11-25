-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_quasiPeriodic_and_independent
-- name    : GlobalTheory.AnArc.quasiPeriodic_and_independent
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:42.961112+00:00
-- url     : https://prove2.me/theorems/fd0c4ae3-a088-4629-91fc-ef09db194998
-- title:
--   An Arc: quasi Periodic and independent
-- statement:
--   The An Arc construction uses the quasi Periodic and independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L644-L682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L644-L682

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.quasiPeriodic_and_independent :
    ((∀ w la v, A.perFactor w la v = Complex.exp (A.lin la v + A.logConst w la)) ∧
      (∀ w la la' v, A.perFactor w (la + la') v = A.perFactor w la (v + A.Pw w la') * A.perFactor w la' v) ∧
      (∀ w la la' v, A.perFactor w la (v + A.Pw w la') * A.perFactor w la' v = A.perFactor w la' (v + A.Pw w la) * A.perFactor w la v) ∧
      (∀ w la la', A.lin la (A.Pw w la') - A.lin la' (A.Pw w la) = -(2 * Real.pi * Complex.I * A.EF la la')) ∧
      ∀ j α, ∀ th ∈ A.Theta j α, ∀ w la v,
        ((Summable fun μ => A.term j α th μ (v + A.Pw w la) * eTwoPi (w * A.exponent j α μ)) ↔
          Summable fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ)) ∧
        A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v) ∧
    (∀ (k : ℕ) [NeZero k],
      (∀ la α th z, A.shift k la α th z =
        eTwoPi ((A.T la.y α + la.n α - A.H (A.ct α) la.l / (2 * Complex.I)) / k) *
          Complex.exp (-(Real.pi * A.H z la.l)) * th (z + (k : ℂ)⁻¹ • (A.ct la.y + la.l))) ∧
      (∀ la α, Set.BijOn (A.shift k la α) (A.Theta k α) (A.Theta k (α + la.y))) ∧
      (∀ la la' α th, A.shift k la (α + la'.y) (A.shift k la' α th) =
        eTwoPi (-(A.EF la la' / k)) • A.shift k la' (α + la.y) (A.shift k la α th)) ∧
      (∀ w la α th v,
        ((Summable fun μ => A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (w * A.exponent k α μ)) ↔
          Summable fun μ =>
            A.term k (α + la.y) (A.shift k la α th) μ v * eTwoPi (w * A.exponent k (α + la.y) μ)) ∧
        A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (v.1 la.y) =
          Complex.exp (Real.pi * A.H v.2 la.l) * eTwoPi (w * A.be la.y α / k) *
            A.Sum k (α + la.y) (A.shift k la α th) w v) ∧
      ∀ (la : A.La) α (m : ℤ), A.be la.y α = k * m → ∀ th v, A.FSumShift k α th la v =
        HahnSeries.single m (Complex.exp (A.lin la v)) * A.FSum k (α + la.y) (A.shift k la α th) v) ∧
    ∀ (j : ℕ) [NeZero j] (C : Type) (I : C → Type) [Fintype C] [∀ c, Fintype (I c)] (rep : C → A.X),
      (∀ c c' μ, rep c = rep c' + j • μ → c = c') →
      ∀ th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ, (∀ c, LinearIndependent ℂ (th c)) →
        (∀ r : ∀ c, I c → LaurentSeries ℂ,
          (∀ v, ∑ c, ∑ i, r c i * A.FSum j (rep c) (th c i) v = 0) → ∀ c i, r c i = 0) ∧
        ∀ w : ℂ, (∀ c i v, Summable fun μ => A.term j (rep c) (th c i) μ v * eTwoPi (w * A.exponent j (rep c) μ)) →
          ∀ r : ∀ c, I c → ℂ, (∀ v, ∑ c, ∑ i, r c i * A.Sum j (rep c) (th c i) w v = 0) → ∀ c i, r c i = 0 := by sorry
