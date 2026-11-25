-- Prove2me | Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_ofTwist_support_periodic_levels
-- name    : GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:53.998474+00:00
-- url     : https://prove2.me/theorems/11f90509-7692-4726-abc3-456df964a292
-- title:
--   Twist Support Periodic Levels: of Twist support periodic levels
-- statement:
--   The Twist Support Periodic Levels construction uses the of Twist support periodic levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L106-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels

theorem GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by sorry
