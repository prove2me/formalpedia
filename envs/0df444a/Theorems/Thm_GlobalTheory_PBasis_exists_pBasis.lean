-- Prove2me | Theorems.Thm_GlobalTheory_PBasis_exists_pBasis
-- name    : GlobalTheory.PBasis.exists_pBasis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:53.623881+00:00
-- url     : https://prove2.me/theorems/de3c8964-a91e-4326-acf9-8e799a398673
-- title:
--   PBasis: exists p Basis
-- statement:
--   The PBasis construction uses the exists p Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L140-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L140-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]

theorem GlobalTheory.PBasis.exists_pBasis : ∀ (k : Type) [Field k] (p : ℕ), p.Prime → (p : k) = 0 → ∃ B : Set k, Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ ∧ ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) → ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b := by sorry
