-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_apply_eq_iff
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.apply_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:36.986356+00:00
-- url     : https://prove2.me/theorems/050a93e7-5006-4a5f-a88b-4da094dce69e
-- title:
--   Is Chart: apply eq iff
-- statement:
--   The Is Chart construction uses the apply eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L86-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L86-L113

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.apply_eq_iff (h : IsChart a b V q) (u v : V.toScheme) :
    q u = q v ↔ ∃ p : P, a p = V.ι u ∧ b p = V.ι v := by sorry
