-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowFormCycle_zero_iff_of_isAlgClosed
-- name    : GlobalTheory.ChowHt.IsChowFormCycle.zero_iff_of_isAlgClosed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:52.332335+00:00
-- url     : https://prove2.me/theorems/c43d7421-73ae-4bcd-a1ae-5c8bb4cffb25
-- title:
--   Is Chow Form Cycle: zero iff of is Alg Closed
-- statement:
--   The Is Chow Form Cycle construction uses the zero iff of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L267-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L267-L277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
open GlobalTheory.ChowHt.IsChowFormCycle
variable {Z Z' : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}

theorem GlobalTheory.ChowHt.IsChowFormCycle.zero_iff_of_isAlgClosed (h : IsChowFormCycle Z e dl f)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔ ∃ P ∈ Z.support,
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ P, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by sorry
