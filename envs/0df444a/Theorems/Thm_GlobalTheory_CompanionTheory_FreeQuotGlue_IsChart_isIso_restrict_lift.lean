-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_isIso_restrict_lift
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.isIso_restrict_lift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:41:20.679851+00:00
-- url     : https://prove2.me/theorems/5a6bd7f9-98fc-443a-a5b1-da180bac4f19
-- title:
--   Is Chart: is Iso restrict lift
-- statement:
--   The Is Chart construction uses the is Iso restrict lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackOfGluedCharts.lean#L19-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackOfGluedCharts.lean#L19-L47

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedCharts
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.isIso_restrict_lift {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {π : X ⟶ Y'} {V : X.Opens}
    {q : V.toScheme ⟶ Y} {em : Y ⟶ Y'} [IsOpenImmersion em] (h : IsChart a b V q)
    (hc : V.ι ≫ π = q ≫ em) (hpre : π ⁻¹ᵁ em.opensRange = V) (w : a ≫ π = b ≫ π) :
    IsIso (pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V)) := by sorry
