-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_eq_zero_of_sum_FSum
-- name    : GlobalTheory.AnArc.eq_zero_of_sum_FSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:56.683241+00:00
-- url     : https://prove2.me/theorems/40d58a6b-0d3d-43ec-ab52-97993965135a
-- title:
--   An Arc: eq zero of sum FSum
-- statement:
--   The An Arc construction uses the eq zero of sum FSum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L624-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L624-L629

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

theorem GlobalTheory.AnArc.eq_zero_of_sum_FSum [NeZero j] (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c))
    {r : ∀ c, I c → LaurentSeries ℂ} (h : ∀ v, ∑ c, ∑ i, r c i * A.FSum j (rep c) (th c i) v = 0) (c : C) (i : I c) :
    r c i = 0 := by sorry
