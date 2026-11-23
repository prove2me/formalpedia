-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_linearIndependent_Sum_sigma
-- name    : GlobalTheory.AnArc.linearIndependent_Sum_sigma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:40.891112+00:00
-- url     : https://prove2.me/theorems/b1133061-3c59-44b7-9568-7545d7fa352c
-- title:
--   An Arc: linear Independent Sum sigma
-- statement:
--   The An Arc construction uses the linear Independent Sum sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L601-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L601-L606

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

theorem GlobalTheory.AnArc.linearIndependent_Sum_sigma (hj : j ≠ 0) (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) (w : ℂ)
    (hs : ∀ c i z, Summable fun μ => A.term j (rep c) (th c i) μ (0, z) * eTwoPi (w * A.exponent j (rep c) μ)) :
    LinearIndependent ℂ fun p : Σ c, I c => A.Sum j (rep p.1) (th p.1 p.2) w := by sorry
