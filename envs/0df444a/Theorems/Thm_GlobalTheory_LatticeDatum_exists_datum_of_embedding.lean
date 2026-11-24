-- Prove2me | Theorems.Thm_GlobalTheory_LatticeDatum_exists_datum_of_embedding
-- name    : GlobalTheory.LatticeDatum.exists_datum_of_embedding
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:35.089639+00:00
-- url     : https://prove2.me/theorems/272ea5ec-6453-41b2-a8a8-f74b241fff96
-- title:
--   Lattice Datum: exists datum of embedding
-- statement:
--   The Lattice Datum construction uses the exists datum of embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeDatumOfSelfDualLattice.lean#L133-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeDatumOfSelfDualLattice.lean#L133-L221

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

theorem GlobalTheory.LatticeDatum.exists_datum_of_embedding (H : Host E) (D : Datum H) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hinj : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ x) (φ y))
    (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L]
    (φ' : L →ₗ[𝓞 E] (Fin r → E)) (hinj' : Function.Injective φ')
    (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (hdual : ∀ v, (∀ y, ∃ n : ℤ, traceHerm ξ Gm v (φ' y) = n) ↔ v ∈ LinearMap.range φ') :
    ∃ (D' : Datum H) (φ'' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧
      LinearMap.range φ'' = LinearMap.range φ' ∧ Function.Injective φ'' ∧
      ∀ x y, ((D'.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ'' x) (φ'' y) := by sorry
