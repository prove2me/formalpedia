-- Prove2me | Theorems.Thm_N25_U25_complex_endpoint_ord_zero
-- name    : N25.U25_complex_endpoint_ord_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:58.99201+00:00
-- url     : https://prove2.me/theorems/eb2defb9-b7e3-4a56-97e2-d76db630f2d7
-- title:
--   A normalized endpoint limit forces modular-unit order zero
-- statement:
--   Fix $i∈ℤ/5ℤ$. Let $x$ have the $i$th unit Laurent series, let $P$ be a complex place, let $B∈SL_2(ℤ)$ have $25∤B_{21}$, and let $w>0$. Assume every nonzero $y$ has the stated nonzero normalized limit along $Bτ$. Then $$ord_P(x)=0.$$ This excludes endpoint zeros and poles.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false
open Filter Topology ModularCurve AlgebraicCurve
open scoped MatrixGroups
open N25

theorem N25.U25_complex_endpoint_ord_zero (i : Fin 5)
    (x : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hx : (x : LaurentSeries ℂ) = unitSeries25 ℂ i)
    (P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)))
    (B : SL(2, ℤ)) (hB : ¬ (25 : ℤ) ∣ B 1 0) (w : ℕ) (hw : 0 < w)
    (hlead : ∀ y : laurentBaseChange ℂ (xHFunctionField 25 N25.H25), y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto
        (fun τ : UpperHalfPlane => realizeOf (CohCarrier.GammaH 25 N25.H25)
          (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (P.ord y : ℂ) * (τ : ℂ) / (w : ℂ))))
        UpperHalfPlane.atImInfty (nhds L)) : P.ord x = 0 := by sorry
