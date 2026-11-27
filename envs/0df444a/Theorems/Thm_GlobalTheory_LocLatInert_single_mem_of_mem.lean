-- Prove2me | Theorems.Thm_GlobalTheory_LocLatInert_single_mem_of_mem
-- name    : GlobalTheory.LocLatInert.single_mem_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:48:44.515085+00:00
-- url     : https://prove2.me/theorems/d059b110-e43e-5231-b9b3-da4a49de166b
-- title:
--   Loc Lat Inert: single mem of mem
-- statement:
--   The Loc Lat Inert construction uses the single mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L50-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L50-L108

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
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.LocLatInert.single_mem_of_mem (σ : K →+* K) {n : ℕ} (L : AddSubgroup (Fin n → K))
    (hO : ∀ a : K, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L)
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (u : K) (hu : σ u * u = 1) (hu1 : Valued.v u ≤ 1) (hu2 : Valued.v (σ u) ≤ 1)
    (hu3 : 1 - u ≠ 0) (hu4 : Valued.v (1 - u)⁻¹ ≤ 1)
    (w : Fin n → K) (hw : w ∈ L) (i : Fin n) : Pi.single i (w i) ∈ L := by sorry
