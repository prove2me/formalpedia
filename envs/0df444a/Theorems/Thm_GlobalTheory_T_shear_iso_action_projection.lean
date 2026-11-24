-- Prove2me | Theorems.Thm_GlobalTheory_T_shear_iso_action_projection
-- name    : GlobalTheory.T.shear_iso_action_projection
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:23.743482+00:00
-- url     : https://prove2.me/theorems/bb6e5d66-6790-4ded-b38e-6cb76afd2514
-- title:
--   T: shear iso action projection
-- statement:
--   The T construction uses the shear iso action projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ShearIsoActionProjectionStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ShearIsoActionProjectionStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ShearIsoActionProjection
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ShearIsoActionProjectionStatement
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

theorem GlobalTheory.T.shear_iso_action_projection : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by sorry
