-- Prove2me | Theorems.Thm_N25_unitAnalytic25_affine_leading_limit
-- name    : N25.unitAnalytic25_affine_leading_limit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:25.845943+00:00
-- url     : https://prove2.me/theorems/659d2df0-02be-4acf-a546-85100a4c9fee
-- title:
--   Affine cusp coordinates give a nonzero leading term for each analytic unit
-- statement:
--   Let $i∈ℤ/5ℤ$, let $A,B∈SL_2(ℤ)$, and let $φ$ be a map of the upper half-plane satisfying $φ(τ)=aτ+b$ with $a>0$ and $Bφ(τ)=25Aτ$. For $x_g=((gB_{00})\bmod 25)/25$, define $β_B(g)=x_g^2-x_g+1/6$, write $(r_{i,1},r_{i,2})$ for the prescribed residue pair, and set $Δ_i=β_B(r_{i,1})+β_B(r_{i,2})-β_B(r_{i+1,1})-β_B(r_{i+1,2})$. Then there is $c∈ℂ^{×}$ such that $$\lim_{\operatorname{Im}τ→∞}\frac{u_i(Aτ)}{\exp(πiaΔ_iτ)}=c.$$ This supplies the precise leading exponent at an arbitrary affine cusp coordinate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open Filter Topology
open N25

theorem N25.unitAnalytic25_affine_leading_limit
    (i : Fin 5) (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (φ : UpperHalfPlane → UpperHalfPlane) (a b : ℝ) (ha : 0 < a)
    (hφ : ∀ τ : UpperHalfPlane, (φ τ : ℂ) = (a : ℂ)*(τ : ℂ)+(b : ℂ))
    (harg : ∀ τ : UpperHalfPlane, ((B • φ τ : UpperHalfPlane) : ℂ) =
      25*((A • τ : UpperHalfPlane) : ℂ)) :
    let β : ℕ → ℝ := fun g =>
      (((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25)^2 -
        ((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25 + 1/6
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto
      (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ) /
        Complex.exp (Real.pi*Complex.I*
          (((β (unitResidues25 i).1+β (unitResidues25 i).2-
            (β (unitResidues25 (i+1)).1+β (unitResidues25 (i+1)).2))*a : ℝ) : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by sorry
