-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_isPeriod
-- name    : GlobalTheory.AnArc.isPeriod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:42:32.59893+00:00
-- url     : https://prove2.me/theorems/760ca666-a323-46e5-9f02-904d12e251e7
-- title:
--   An Arc: is Period
-- statement:
--   The An Arc construction uses the is Period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L485-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L485-L492

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
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
open Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem GlobalTheory.AnArc.isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    (A : AnArc (𝓞 E)) {w : ℂ} (hw : (A.BwMat w).PosDef) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (hh : ∀ (a : 𝓞 E) v i, h (A.actV a v) i = ty i (a : E) * h v i)
    (e : D.La ≃+ A.La) (he : ∀ (a : 𝓞 E) x, e (a • x) = a • e x) (hE : ∀ x y, A.EF (e x) (e y) = D.EF x y)
    (P : D.La →+ (Fin g → ℂ)) (hP : ∀ x, P x = h (A.Pw w (e x))) : IsPeriod D ty P := by sorry
