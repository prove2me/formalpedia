-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_linearIndependent_Sum
-- name    : GlobalTheory.AnArc.linearIndependent_Sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:37.580358+00:00
-- url     : https://prove2.me/theorems/c1e15ff3-5ee6-4635-ac88-b93f3fad0797
-- title:
--   An Arc: linear Independent Sum
-- statement:
--   The An Arc construction uses the linear Independent Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L519-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L519-L534

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

theorem GlobalTheory.AnArc.linearIndependent_Sum {j : ℕ} (hj : j ≠ 0) {ι : Type*} (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') (th : ι → (Fin A.gB → ℂ) → ℂ)
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) (w : ℂ)
    (hs : ∀ p z, Summable fun μ => A.term j (wt p) (th p) μ (0, z) * eTwoPi (w * A.exponent j (wt p) μ)) :
    LinearIndependent ℂ fun p => A.Sum j (wt p) (th p) w := by sorry
