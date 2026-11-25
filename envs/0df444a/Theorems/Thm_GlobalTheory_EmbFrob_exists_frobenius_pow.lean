-- Prove2me | Theorems.Thm_GlobalTheory_EmbFrob_exists_frobenius_pow
-- name    : GlobalTheory.EmbFrob.exists_frobenius_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:26:38.067447+00:00
-- url     : https://prove2.me/theorems/64535a1a-2d9b-4af3-93ef-405fdfe14222
-- title:
--   Emb Frob: exists frobenius pow
-- statement:
--   The Emb Frob construction uses the exists frobenius pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPowOfFiniteField.lean#L64-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPowOfFiniteField.lean#L64-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbFrob
open Polynomial
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

theorem GlobalTheory.EmbFrob.exists_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Finite ℤ OE] (C : Type) [Field C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R],
    v.Integers R → ¬ IsUnit (p : R) → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE)
    (σ τ : OE →+* R), σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    τ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    ∃ i : ℕ, ∀ a : OE, v (algebraMap R C (τ a - σ a ^ (p ^ i))) < 1 := by sorry
