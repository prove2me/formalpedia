-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimeAvoid_exists_basicOpen_between
-- name    : GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:23.512802+00:00
-- url     : https://prove2.me/theorems/7bd328c3-9952-4a80-875e-6a7aa4772711
-- title:
--   Prime Avoid: exists basic Open between
-- statement:
--   The Prime Avoid construction uses the exists basic Open between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteSetBasicOpenAffine.lean#L12-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteSetBasicOpenAffine.lean#L12-L50

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteSetBasicOpenAffine
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimeAvoid

theorem GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between {X : Scheme.{0}} (U V₀ : X.Opens) (hU : IsAffineOpen U)
    (hV : V₀ ≤ U) (K : Set X) (hK : K.Finite) (hKV : K ⊆ V₀) :
    ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by sorry
