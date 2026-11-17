-- Prove2me | Theorems.Thm_N25_unitAnalytic25_A13
-- name    : N25.unitAnalytic25_A13
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:25.601245+00:00
-- url     : https://prove2.me/theorems/c89075a9-a247-441a-8aad-5175dafc72bc
-- title:
--   The matrix $\begin{psmallmatrix}13&1\25&2\end{psmallmatrix}$ cyclically permutes the five analytic units
-- statement:
--   Let $u_i(τ)$, for $i∈ℤ/5ℤ$, be the five unpowered analytic Siegel-unit ratios at level $25$, and let $A=\begin{pmatrix}13&1\25&2\end{pmatrix}$. Define $(ε_0,ε_1,ε_2,ε_3,ε_4)=(-1,-1,1,-1,-1)$. Then for every $i$ and every upper-half-plane point $τ$, $$u_i(Aτ)=ε_i\,u_{i-1}(τ),$$ where the index $i-1$ is taken modulo $5$. This transformation law supplies the cyclic unit relations used to compute cusp divisors.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_A13 (i : Fin 5) (τ : UpperHalfPlane) :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
    let ε : Fin 5 → ℂ := ![-1,-1,1,-1,-1]
    unitAnalytic25 i (A • τ) = ε i * unitAnalytic25 (i-1) τ := by sorry
