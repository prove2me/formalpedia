-- Prove2me | Theorems.Thm_N25_unitAnalytic25_A7
-- name    : N25.unitAnalytic25_A7
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:20.390198+00:00
-- url     : https://prove2.me/theorems/dfb233dd-4f72-4351-a4d4-6ce8255f5415
-- title:
--   The matrix $\begin{psmallmatrix}7&5\25&18\end{psmallmatrix}$ fixes every analytic unit
-- statement:
--   Let $i∈ℤ/5ℤ$, let $τ$ lie in the complex upper half-plane, and put $A=\begin{psmallmatrix}7&5\25&18\end{psmallmatrix}∈SL_2(ℤ)$. For the $i$th analytic level-$25$ modular unit $u_i$, $$u_i(Aτ)=u_i(τ).$$ This is one of the explicit generator transformations used to prove invariance under the level subgroup.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_A7 (i : Fin 5) (τ : UpperHalfPlane) :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![7,5;25,18], by norm_num [Matrix.det_fin_two]⟩
    unitAnalytic25 i (A • τ) = unitAnalytic25 i τ := by sorry
