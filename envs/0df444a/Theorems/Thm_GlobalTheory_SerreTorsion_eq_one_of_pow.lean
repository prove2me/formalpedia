-- Prove2me | Theorems.Thm_GlobalTheory_SerreTorsion_eq_one_of_pow
-- name    : GlobalTheory.SerreTorsion.eq_one_of_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:09.550696+00:00
-- url     : https://prove2.me/theorems/91196144-d708-41cc-8bb2-5e2b27d5d1a7
-- title:
--   Serre Torsion: eq one of pow
-- statement:
--   The Serre Torsion construction uses the eq one of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqOneOfPowEqOneOfCongrOne.lean#L83-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqOneOfPowEqOneOfCongrOne.lean#L83-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SerreTorsion
variable {E : Type} [Ring E]

theorem GlobalTheory.SerreTorsion.eq_one_of_pow (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (m : ℕ) :
    m ≠ 0 → ∀ ψ : E, (1 + c • ψ) ^ m = 1 → 1 + c • ψ = 1 := by sorry
