-- Prove2me | Theorems.Thm_N25_siegelDilation_gamma0
-- name    : N25.siegelDilation_gamma0
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:04.610214+00:00
-- url     : https://prove2.me/theorems/d9e34049-64a1-4a24-9f31-cb9bac129e92
-- title:
--   Level-$25$ Siegel functions satisfy a dilation law on $Γ_0(25)$
-- statement:
--   Let $A=\begin{pmatrix}a&b\c&d\end{pmatrix}∈SL_2(ℤ)$ with $25∣c$, and write $g_{r,s}^{(25)}(z)$ for the level-$25$ Siegel function. There exists $μ∈ℂ$ with $μ^{12}=1$ such that for every integer $m$ and every upper-half-plane point $τ$, $$-g_{m,0}^{(25)}(25Aτ)=μ\exp\big(πi(abm^2/25-bm)\big)\big(-g_{am,0}^{(25)}(25τ)\big).$$ This is the transformation law used to prove modularity of the analytic unit ratios.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

theorem N25.siegelDilation_gamma0
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : (25 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ μ : ℂ, μ^12 = 1 ∧ ∀ (g : ℤ) (τ : UpperHalfPlane),
      -ModularCurve.siegelFun 25 g 0 (25 * ((A • τ : UpperHalfPlane) : ℂ)) =
        μ * Complex.exp (Real.pi * Complex.I *
          (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) *
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (g : ℂ)^2 / 25 -
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (g : ℂ))) *
          (-ModularCurve.siegelFun 25
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * g) 0 (25 * (τ : ℂ))) := by sorry
