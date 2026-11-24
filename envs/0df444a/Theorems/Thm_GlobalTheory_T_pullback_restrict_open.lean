-- Prove2me | Theorems.Thm_GlobalTheory_T_pullback_restrict_open
-- name    : GlobalTheory.T.pullback_restrict_open
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:55:36.133831+00:00
-- url     : https://prove2.me/theorems/1bb4ee49-5ede-440b-8177-97ac311fab31
-- title:
--   T: pullback restrict open
-- statement:
--   The T construction uses the pullback restrict open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackRestrictOpenStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackRestrictOpenStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackRestrictOpen
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackRestrictOpenStatement
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
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pullback_restrict_open : ∀ {P Q Y S : Scheme.{0}} {c : P ⟶ Q} {v : P ⟶ Y} {g : Q ⟶ S} {p : Y ⟶ S}, IsPullback c v g p → ∀ (W : S.Opens) (D : Y.Opens), D ≤ p ⁻¹ᵁ W → ∃ (h : D.toScheme ⟶ W.toScheme) (u : (v ⁻¹ᵁ D).toScheme ⟶ (g ⁻¹ᵁ W).toScheme), IsPullback u (v ∣_ D) (g ∣_ W) h := by sorry
