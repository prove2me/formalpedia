-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_eq_zero_of_sum_Sum
-- name    : GlobalTheory.AnArc.eq_zero_of_sum_Sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:44.756942+00:00
-- url     : https://prove2.me/theorems/1f325104-4298-4c44-9918-6999a4c4bba9
-- title:
--   An Arc: eq zero of sum Sum
-- statement:
--   The An Arc construction uses the eq zero of sum Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L616-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L616-L622

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
variable {C : Type*} {I : C → Type*} {j : ℕ} {rep : C → A.X}
variable [Fintype C] [∀ c, Fintype (I c)]

theorem GlobalTheory.AnArc.eq_zero_of_sum_Sum (hj : j ≠ 0) (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) {w : ℂ}
    (hs : ∀ c i z, Summable fun μ => A.term j (rep c) (th c i) μ (0, z) * eTwoPi (w * A.exponent j (rep c) μ))
    {r : ∀ c, I c → ℂ} (h : ∀ v, ∑ c, ∑ i, r c i * A.Sum j (rep c) (th c i) w v = 0) (c : C) (i : I c) :
    r c i = 0 := by sorry
