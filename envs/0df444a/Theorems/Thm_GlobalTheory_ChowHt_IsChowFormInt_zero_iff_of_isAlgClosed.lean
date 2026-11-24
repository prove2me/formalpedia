-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_zero_iff_of_isAlgClosed
-- name    : GlobalTheory.ChowHt.IsChowFormInt.zero_iff_of_isAlgClosed
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:39.757696+00:00
-- url     : https://prove2.me/theorems/7ab8b69e-ea87-44b9-ae99-fec44dec116b
-- title:
--   Is Chow Form Int: zero iff of is Alg Closed
-- statement:
--   The Is Chow Form Int construction uses the zero iff of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L117-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L117-L133

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
open GlobalTheory.ChowHt.IsChowFormInt
variable {I : Ideal (MvPolynomial (Fin N) k)} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}

theorem GlobalTheory.ChowHt.IsChowFormInt.zero_iff_of_isAlgClosed (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k))
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by sorry
