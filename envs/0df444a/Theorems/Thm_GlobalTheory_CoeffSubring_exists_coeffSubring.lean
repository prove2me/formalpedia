-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_exists_coeffSubring
-- name    : GlobalTheory.CoeffSubring.exists_coeffSubring
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:58.57634+00:00
-- url     : https://prove2.me/theorems/b722bb76-d5f8-4edd-a439-e8b489003908
-- title:
--   Coeff Subring: exists coeff Subring
-- statement:
--   The Coeff Subring construction uses the exists coeff Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L231-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L231-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}

theorem GlobalTheory.CoeffSubring.exists_coeffSubring [IsDomain S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (hp : p.Prime) (hp0 : (p : S) ≠ 0) (h0 : (p : S) ∈ maximalIdeal S) {B : Set (ResidueField S)}
    (hB : Subring.closure (Set.range (fun x : ResidueField S => x ^ p) ∪ B) = ⊤)
    (hB' : ∀ (Q : Type) [CommRing Q] (f : ResidueField S →+* Q) (g : ResidueField S → Q),
      (∀ b ∈ B, g b ^ p = f b) →
      ∃ σ : ResidueField S →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b) :
    ∃ Λ : Subring S, (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) ∧
      (∀ a : Λ, (a : S) ∈ maximalIdeal S → (p : Λ) ∣ a) ∧
      (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) := by sorry
