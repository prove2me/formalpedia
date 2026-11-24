-- Prove2me | Theorems.Thm_GlobalTheory_DetIdeal_det_mul_vol_mul_conj
-- name    : GlobalTheory.DetIdeal.det_mul_vol_mul_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:30.244711+00:00
-- url     : https://prove2.me/theorems/b66ac3cd-d17e-41c0-8191-c0ecff341ff3
-- title:
--   Det Ideal: det mul vol mul conj
-- statement:
--   The Det Ideal construction uses the det mul vol mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L230-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L230-L321

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.DetIdeal.det_mul_vol_mul_conj (H : Host E) (D : Datum H) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : FD.cc ξ = -ξ) (hξ0 : ξ ≠ 0)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (n : 𝓞 E) (hn : n ≠ 0)
    (hint : ∀ z, ∃ x : Fin r → 𝓞 E, algebraMap (𝓞 E) E ∘ x = algebraMap (𝓞 E) E n • φ z) :
    ∃ I : Ideal (𝓞 E), I ≠ ⊥ ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((ξ / ((n : E) * FD.cc (n : E))) ^ r * Gm.det) *
        ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ^ r := by sorry
