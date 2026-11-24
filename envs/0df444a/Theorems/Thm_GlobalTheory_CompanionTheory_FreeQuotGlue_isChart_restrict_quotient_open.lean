-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_isChart_restrict_quotient_open
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:41:38.383207+00:00
-- url     : https://prove2.me/theorems/c775d6f2-c39b-4cbc-a85a-48043bf68299
-- title:
--   Free Quot Glue: is Chart restrict quotient open
-- statement:
--   The Free Quot Glue construction uses the is Chart restrict quotient open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ChartRestrictPreimageOpen.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ChartRestrictPreimageOpen.lean#L104-L114

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open :
    ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y},
      IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V)
        (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme),
        IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by sorry
