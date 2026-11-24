-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_span_eq_radical_elimIdeal
-- name    : GlobalTheory.ChowHt.IsChowFormInt.span_eq_radical_elimIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:44.796152+00:00
-- url     : https://prove2.me/theorems/905c6054-f4af-4deb-980c-33735fc90d78
-- title:
--   Is Chow Form Int: span eq radical elim Ideal
-- statement:
--   The Is Chow Form Int construction uses the span eq radical elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L106-L115

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

theorem GlobalTheory.ChowHt.IsChowFormInt.span_eq_radical_elimIdeal (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := by sorry
