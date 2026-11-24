-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_exists_opens_image_preimage
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:41:20.819392+00:00
-- url     : https://prove2.me/theorems/1308dc69-24c5-4658-a6e2-e42961db2606
-- title:
--   Is Chart: exists opens image preimage
-- statement:
--   The Is Chart construction uses the exists opens image preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/InvariantOpenChartPreimage.lean#L13-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/InvariantOpenChartPreimage.lean#L13-L42

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimage
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens}
    {q : V.toScheme ⟶ Y} (h : IsChart a b V q) (V' : X.Opens) (hV : V' ≤ V)
    (hs : a ⁻¹ᵁ V' = b ⁻¹ᵁ V') : ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by sorry
