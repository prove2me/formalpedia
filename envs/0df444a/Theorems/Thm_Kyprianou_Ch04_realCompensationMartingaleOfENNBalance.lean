-- Prove2me | Theorems.Thm_Kyprianou_Ch04_realCompensationMartingaleOfENNBalance
-- name    : Kyprianou.Ch04.realCompensationMartingaleOfENNBalance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T09:54:58.055228+00:00
-- url     : https://prove2.me/theorems/d92c6d22-43a4-5c26-9df4-c50f0b8cdfe1
-- title:
--   Martingale from finite compensated extended clock balance
-- statement:
--   Finite extended clock expectations imply real integrability. Eventwise extended balance gives real set-integral equality after conversion; conditional expectation uniqueness constructs the martingale.
-- source:
--   Kyprianou (2006), corrected Corollary 4.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.realCompensationMartingaleOfENNBalance
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (J C : NNReal → Omega → ENNReal)
    (j c : NNReal → Omega → Real)
    (hj : StronglyAdapted F j) (hc : StronglyAdapted F c)
    (hJ : ∀ t, Measurable (J t)) (hC : ∀ t, Measurable (C t))
    (hfinJ : ∀ t, (∫⁻ w, J t w ∂P) < ⊤)
    (hfinC : ∀ t, (∫⁻ w, C t w ∂P) < ⊤)
    (heJ : ∀ t, j t =ᵐ[P] fun w => (J t w).toReal)
    (heC : ∀ t, c t =ᵐ[P] fun w => (C t w).toReal)
    (hbal : ∀ u t : NNReal, u ≤ t → ∀ A : Set Omega, MeasurableSet[F u] A →
      (∫⁻ w in A, J t w ∂P) + (∫⁻ w in A, C u w ∂P) =
      (∫⁻ w in A, J u w ∂P) + (∫⁻ w in A, C t w ∂P)) :
    Martingale (fun t w => j t w - c t w) F P := by
  sorry
