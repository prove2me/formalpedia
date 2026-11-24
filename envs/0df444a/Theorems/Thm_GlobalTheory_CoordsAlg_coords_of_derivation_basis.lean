-- Prove2me | Theorems.Thm_GlobalTheory_CoordsAlg_coords_of_derivation_basis
-- name    : GlobalTheory.CoordsAlg.coords_of_derivation_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:49.917349+00:00
-- url     : https://prove2.me/theorems/bc238761-92de-407f-90a8-7f9c3f1997b3
-- title:
--   Coords Alg: coords of derivation basis
-- statement:
--   The Coords Alg construction uses the coords of derivation basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationFamilyCotangentBasis.lean#L18-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationFamilyCotangentBasis.lean#L18-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoordsAlg

theorem GlobalTheory.CoordsAlg.coords_of_derivation_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by sorry
