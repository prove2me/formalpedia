-- Prove2me | Theorems.Thm_GlobalTheory_orbit_count_parabolic_unfold
-- name    : GlobalTheory.orbit_count_parabolic_unfold
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:16.030164+00:00
-- url     : https://prove2.me/theorems/1e17d130-644c-4104-84e1-93aa213d9bd0
-- title:
--   Global Theory: orbit count parabolic unfold
-- statement:
--   The Global Theory construction uses the orbit count parabolic unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitCountParabolicUnfoldLevi.lean#L5-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitCountParabolicUnfoldLevi.lean#L5-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitCountParabolicUnfoldLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.orbit_count_parabolic_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by sorry
