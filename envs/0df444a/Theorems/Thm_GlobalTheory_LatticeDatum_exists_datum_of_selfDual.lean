-- Prove2me | Theorems.Thm_GlobalTheory_LatticeDatum_exists_datum_of_selfDual
-- name    : GlobalTheory.LatticeDatum.exists_datum_of_selfDual
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:56.451884+00:00
-- url     : https://prove2.me/theorems/61bacaaf-ce6b-4b08-b441-42966e47e47e
-- title:
--   Lattice Datum: exists datum of self Dual
-- statement:
--   The Lattice Datum construction uses the exists datum of self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeDatumOfSelfDualLattice.lean#L223-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeDatumOfSelfDualLattice.lean#L223-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.LatticeDatum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.LatticeDatum.exists_datum_of_selfDual (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (Λ' : Submodule (𝓞 E) (Fin r → E)) (_hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
      Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (hfg : Λ'.FG) (hspan' : Submodule.span E (Λ' : Set (Fin r → E)) = ⊤)
    (hdual : ∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') :
    ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧
      (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
        Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by sorry
