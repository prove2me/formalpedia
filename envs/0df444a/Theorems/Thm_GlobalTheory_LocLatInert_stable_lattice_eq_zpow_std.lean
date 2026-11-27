-- Prove2me | Theorems.Thm_GlobalTheory_LocLatInert_stable_lattice_eq_zpow_std
-- name    : GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:54:22.811818+00:00
-- url     : https://prove2.me/theorems/03a60001-f408-417d-bb9b-5a5269938815
-- title:
--   Loc Lat Inert: stable lattice eq zpow std
-- statement:
--   The Loc Lat Inert construction uses the stable lattice eq zpow std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L186-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L186-L244

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert

theorem GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by sorry
