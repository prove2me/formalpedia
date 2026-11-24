-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_scale_latOf
-- name    : GlobalTheory.AdLat.scale_latOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:09.42446+00:00
-- url     : https://prove2.me/theorems/662fe8c2-db89-476b-97b0-d23b495ab637
-- title:
--   Ad Lat: scale lat Of
-- statement:
--   The Ad Lat construction uses the scale lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZeroMemLatOf.lean#L103-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZeroMemLatOf.lean#L103-L251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZeroMemLatOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
open Scale
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

theorem GlobalTheory.AdLat.scale_latOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (I : FractionalIdeal (𝓞 E)⁰ E) (L' : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → I ≠ 0 → L' = Submodule.span (𝓞 E) {w | ∃ a ∈ I, ∃ x ∈ L, w = a • x} → ((Submodule.span (𝓞 E) {w | ∃ a ∈ I, ∃ v ∈ _root_.GlobalTheory.AdLat.latOf F (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) L, w = a • v} : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = _root_.GlobalTheory.AdLat.latOf F (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) L' ∧ (AddSubgroup.closure {w | ∃ a ∈ I, ∃ z ∈ (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)).mulVec '' (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * z i} : Set (Fin n → _root_.GlobalTheory.AdLat.RA F E)) = (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)).mulVec '' (_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E))) ∧ L'.FG ∧ Submodule.span E (L' : Set (Fin n → E)) = ⊤ := by sorry
