-- Prove2me | Theorems.Thm_N25_cusp_complex_order_zero_of_nonzero_limit
-- name    : N25.cusp_complex_order_zero_of_nonzero_limit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:28.26302+00:00
-- url     : https://prove2.me/theorems/dc84c522-e3f9-4142-b60a-037abeabed5e
-- title:
--   A nonzero finite cusp limit forces valuation zero
-- statement:
--   Let $P$ be a place of the complex level-$25$ function field, let $B\in\mathrm{SL}_2(\mathbb Z)$, and let $w>0$. Assume every nonzero function $y$ has a nonzero normalized leading limit $y(B\tau)\exp(-2\pi i\operatorname{ord}_P(y)\tau/w)$. If the realization of $x$ along $B\tau$ tends to a nonzero complex number $c$, then
--
--   $$x\ne0\quad\text{and}\quad\operatorname{ord}_P(x)=0.$$
--
--   This detects units in the cusp valuation ring from nonzero analytic limits.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false
open Filter Topology ModularCurve AlgebraicCurve UpperHalfPlane
open scoped MatrixGroups
open N25

theorem N25.cusp_complex_order_zero_of_nonzero_limit
    (P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)))
    (B : SL(2, ℤ)) (w : ℕ) (hw : 0 < w)
    (hlead : ∀ y : laurentBaseChange ℂ (xHFunctionField 25 N25.H25), y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto
        (fun τ : UpperHalfPlane => realizeOf (CohCarrier.GammaH 25 N25.H25)
          (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (P.ord y : ℂ) * (τ : ℂ) / (w : ℂ))))
        UpperHalfPlane.atImInfty (nhds L))
    (x : laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) (c : ℂ) (hc : c ≠ 0)
    (hf : Tendsto (fun τ : UpperHalfPlane =>
      realizeOf (CohCarrier.GammaH 25 N25.H25) (x : LaurentSeries ℂ) (B • τ))
      UpperHalfPlane.atImInfty (nhds c)) : x ≠ 0 ∧ P.ord x = 0 := by sorry
