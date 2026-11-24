-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_free_pullback_affine
-- name    : GlobalTheory.T.finite_free_pullback_affine
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:40:05.940065+00:00
-- url     : https://prove2.me/theorems/b2b7ad35-3548-4f4a-9880-40ead0594c42
-- title:
--   T: finite free pullback affine
-- statement:
--   The T construction uses the finite free pullback affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreePullbackAffineStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreePullbackAffineStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffineStatement
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

theorem GlobalTheory.T.finite_free_pullback_affine : ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by sorry
