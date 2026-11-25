-- Prove2me | Theorems.Thm_GlobalTheory_T_etale_coordinates_differentials
-- name    : GlobalTheory.T.etale_coordinates_differentials
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:44.282781+00:00
-- url     : https://prove2.me/theorems/0c250ed3-3ffc-4a7c-994c-f64fe01f7a5c
-- title:
--   T: etale coordinates differentials
-- statement:
--   The T construction uses the etale coordinates differentials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/EtaleCoordinatesDifferentials.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/EtaleCoordinatesDifferentials.lean#L4-L5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinatesDifferentials
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_EtaleCoordinatesDifferentials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial

theorem GlobalTheory.T.etale_coordinates_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by sorry
