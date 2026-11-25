-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_span_eq_elimIdeal
-- name    : GlobalTheory.ChowHt.IsChowFormInt.span_eq_elimIdeal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:41.50309+00:00
-- url     : https://prove2.me/theorems/e07e92d8-adda-4293-ac9a-d504e1961411
-- title:
--   Is Chow Form Int: span eq elim Ideal
-- statement:
--   The Is Chow Form Int construction uses the span eq elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L142-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L142-L149

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

theorem GlobalTheory.ChowHt.IsChowFormInt.span_eq_elimIdeal (h : IsChowFormInt I e dl f) (hp : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I := by sorry
