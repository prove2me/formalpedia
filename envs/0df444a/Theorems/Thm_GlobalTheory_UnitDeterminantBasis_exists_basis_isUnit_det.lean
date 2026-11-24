-- Prove2me | Theorems.Thm_GlobalTheory_UnitDeterminantBasis_exists_basis_isUnit_det
-- name    : GlobalTheory.UnitDeterminantBasis.exists_basis_isUnit_det
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:23.105633+00:00
-- url     : https://prove2.me/theorems/f42f55cc-9bc6-4e33-bd5f-f6c5fb6a407b
-- title:
--   Unit Determinant Basis: exists basis is Unit det
-- statement:
--   The Unit Determinant Basis construction uses the exists basis is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitDeterminantBasis.lean#L31-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitDeterminantBasis.lean#L31-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitDeterminantBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.UnitDeterminantBasis

theorem GlobalTheory.UnitDeterminantBasis.exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R], v.Integers R → (∀ σ σ' : OE →+* R, (∀ a : OE, v (algebraMap R C (σ a - σ' a)) < 1) → σ = σ') → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e), ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e) : OE →+* R) (b i : TensorProduct ℤ ℤ_[p] OE))) := by sorry
