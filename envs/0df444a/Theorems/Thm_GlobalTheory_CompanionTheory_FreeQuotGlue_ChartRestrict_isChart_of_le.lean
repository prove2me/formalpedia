-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_ChartRestrict_isChart_of_le
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict.isChart_of_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:41:19.347807+00:00
-- url     : https://prove2.me/theorems/74aba544-fa47-4c91-9ca2-e1ebd5043eed
-- title:
--   Chart Restrict: is Chart of le
-- statement:
--   The Chart Restrict construction uses the is Chart of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ChartRestrictPreimageOpen.lean#L24-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ChartRestrictPreimageOpen.lean#L24-L98

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict.isChart_of_le {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
    (h : IsChart a b V q) (D : Y.Opens) (W : X.Opens) (hle : W ≤ V)
    (hW : ∀ u : V.toScheme, V.ι u ∈ W ↔ q u ∈ D) :
    ∃ q' : W.toScheme ⟶ D.toScheme, IsChart a b W q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by sorry
