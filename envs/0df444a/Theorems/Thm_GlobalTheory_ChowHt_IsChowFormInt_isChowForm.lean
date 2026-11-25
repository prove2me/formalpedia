-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_isChowForm
-- name    : GlobalTheory.ChowHt.IsChowFormInt.isChowForm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:34.386805+00:00
-- url     : https://prove2.me/theorems/d12a8252-523f-4677-9ee1-30fe9f44b8a2
-- title:
--   Is Chow Form Int: is Chow Form
-- statement:
--   The Is Chow Form Int construction uses the is Chow Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L71-L73

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

theorem GlobalTheory.ChowHt.IsChowFormInt.isChowForm (h : IsChowFormInt I e dl f)
    (hf : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)) :
    IsChowForm I e dl f := by sorry
