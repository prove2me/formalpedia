-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_not_mem_prime_iff
-- name    : GlobalTheory.T.norm_not_mem_prime_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:29.236768+00:00
-- url     : https://prove2.me/theorems/31c39f1e-2dc8-4021-839b-eb9ff5407837
-- title:
--   T: norm not mem prime iff
-- statement:
--   The T construction uses the norm not mem prime iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/NormNotMemPrimeIffStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/NormNotMemPrimeIffStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIff
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIffStatement
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

theorem GlobalTheory.T.norm_not_mem_prime_iff : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (e : B) (p : Ideal A), p.IsPrime → (Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q) := by sorry
