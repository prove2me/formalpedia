-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_hasAffineChart_iff
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.hasAffineChart_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:02.891686+00:00
-- url     : https://prove2.me/theorems/bcd722cf-382b-4e7a-8026-1a6e1684ee1d
-- title:
--   Free Quot Glue: has Affine Chart iff
-- statement:
--   The Free Quot Glue construction uses the has Affine Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L19-L25

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

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.hasAffineChart_iff {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) :
    HasAffineChart a b V ↔ ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y), IsAffine Y ∧ IsChart a b V q := by sorry
