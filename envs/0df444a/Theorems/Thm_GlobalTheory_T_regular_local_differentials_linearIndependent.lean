-- Prove2me | Theorems.Thm_GlobalTheory_T_regular_local_differentials_linearIndependent
-- name    : GlobalTheory.T.regular_local_differentials_linearIndependent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:24.041854+00:00
-- url     : https://prove2.me/theorems/3a4933cf-c2d2-5171-9f0c-e704f6da66a0
-- title:
--   T: regular local differentials linear Independent
-- statement:
--   The T construction uses the regular local differentials linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/RegularLocalDifferentialsLinearIndependent.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/RegularLocalDifferentialsLinearIndependent.lean#L4-L5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RegularLocalDifferentialsBasis
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_RegularLocalDifferentialsLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial

theorem GlobalTheory.T.regular_local_differentials_linearIndependent : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by sorry
