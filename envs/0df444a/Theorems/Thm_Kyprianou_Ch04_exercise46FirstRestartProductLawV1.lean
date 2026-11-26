-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstRestartProductLawV1
-- name    : Kyprianou.Ch04.exercise46FirstRestartProductLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T09:08:00.933924+00:00
-- url     : https://prove2.me/theorems/c7ec11a9-4bcb-4c9a-bee7-94c4fcf66fd8
-- title:
--   First service mark and shifted future increments have product law
-- statement:
--   At an almost surely finite stopping time, the service mark is measurable with respect to the stopped information. Apply the right-continuous-filtration strong Markov law and remove the full-measure finite-clock restriction; this gives the joint product law of the service mark and future increments.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstRestartProductLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFin : ∀ᵐ w ∂P, A w ≠ ⊤) :
    let a : Omega → NNReal := fun w => (A w).untopD 0
    let J : Omega → Real := fun w =>
      -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w))
    let Z : Omega → (NNReal → Real) := fun w u => L.X (a w + u) w - L.X (a w) w
    let Y : Omega → (NNReal → Real) := fun w u => L.X u w
    P.map (fun w => (J w, Z w)) = (P.map J).prod (P.map Y) := by
  sorry
