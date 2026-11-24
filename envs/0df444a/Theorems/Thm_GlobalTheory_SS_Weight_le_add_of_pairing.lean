-- Prove2me | Theorems.Thm_GlobalTheory_SS_Weight_le_add_of_pairing
-- name    : GlobalTheory.SS.Weight.le_add_of_pairing
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:18.724263+00:00
-- url     : https://prove2.me/theorems/f7a2821c-7b80-4dcf-a85e-19bb42f5924a
-- title:
--   Weight: le add of pairing
-- statement:
--   The Weight construction uses the le add of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightLeAddOfTorsionPairing.lean#L246-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightLeAddOfTorsionPairing.lean#L246-L376

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors

theorem GlobalTheory.SS.Weight.le_add_of_pairing (M A : Type) [AddCommGroup M] [AddCommGroup A] (l q g t a c C : ℕ)
    (hl : l.Prime) (hl3 : 3 ≤ l) (hq : 2 ≤ q) (hc : 1 ≤ c)
    (hA : ∀ n, Nat.card {x : A // l ^ n • x = 0} = l ^ n)
    (hM : ∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (n * (2 * g)))
    (e : ℕ → M → M → A)
    (he1 : ∀ n x x' y, l ^ n • x = 0 → l ^ n • x' = 0 → l ^ n • y = 0 →
      e n (x + x') y = e n x y + e n x' y ∧ e n y x = - e n x y)
    (he2 : ∀ n x y, l ^ (n + 1) • x = 0 → l ^ n • y = 0 → e (n + 1) x y = e n (l • x) y)
    (he3 : ∀ n x, l ^ n • x = 0 → (∀ y, l ^ n • y = 0 → e n x y = 0) → x = 0)
    (S Φ : M ≃+ M)
    (hSΦ : ∀ n x y, l ^ n • x = 0 → l ^ n • y = 0 →
      e n (S x) (S y) = e n x y ∧ e n (Φ x) (Φ y) = q • e n x y)
    (hcomm : ∀ n x, l ^ n • x = 0 → Φ (S x) = S^[q] (Φ x))
    (hS1 : ∀ x, l • x = 0 → S x = x) (H W : AddSubgroup M) (P : Polynomial ℤ)
    (hH : ∀ n x, l ^ n • x = 0 → S x = x → c • x ∈ H)
    (hcard : ∀ n, Nat.card {x : H // l ^ n • x = 0} ≤ C * l ^ (n * (t + 2 * a)) ∧
      Nat.card {x : W // l ^ n • x = 0} ≤ C * l ^ (n * t))
    (hP : ∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q)
    (hW : ∀ n, ∀ x ∈ W, l ^ n • x = 0 → Φ x = q • x)
    (hPW : ∀ n, ∀ x ∈ H, l ^ n • x = 0 →
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Φ^[j] x) ∈ W) : g ≤ t + a := by sorry
