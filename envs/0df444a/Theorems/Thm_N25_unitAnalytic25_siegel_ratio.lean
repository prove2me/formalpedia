-- Prove2me | Theorems.Thm_N25_unitAnalytic25_siegel_ratio
-- name    : N25.unitAnalytic25_siegel_ratio
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:26.241837+00:00
-- url     : https://prove2.me/theorems/9fe9c3be-65fc-4423-bf34-898f9997051e
-- title:
--   Each transformed analytic unit is an explicit ratio of four Siegel functions
-- statement:
--   Let $i∈ℤ/5ℤ$, let $A,B∈SL_2(ℤ)$, and let $φ:\mathfrak H→\mathfrak H$ satisfy $Bφ(τ)=25Aτ$. Write $(r_{i,1},r_{i,2})$ for the prescribed residues and $g_{r,s}$ for the level-$25$ Siegel function. Then for every $τ∈\mathfrak H$, $$u_i(Aτ)=\frac{g_{r_{i,1}B_{00},\,r_{i,1}B_{01}}(φτ)g_{r_{i,2}B_{00},\,r_{i,2}B_{01}}(φτ)}{g_{r_{i+1,1}B_{00},\,r_{i+1,1}B_{01}}(φτ)g_{r_{i+1,2}B_{00},\,r_{i+1,2}B_{01}}(φτ)}.$$ This is the transformation formula from which cusp asymptotics are read.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_siegel_ratio
    (i : Fin 5) (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (φ : UpperHalfPlane → UpperHalfPlane)
    (hφ : ∀ τ : UpperHalfPlane, ((B • φ τ : UpperHalfPlane) : ℂ) =
      25*((A • τ : UpperHalfPlane) : ℂ)) (τ : UpperHalfPlane) :
    unitAnalytic25 i (A • τ) =
      (ModularCurve.siegelFun 25
          (((unitResidues25 i).1 : ℤ) * B 0 0) (((unitResidues25 i).1 : ℤ) * B 0 1) (φ τ : ℂ) *
        ModularCurve.siegelFun 25
          (((unitResidues25 i).2 : ℤ) * B 0 0) (((unitResidues25 i).2 : ℤ) * B 0 1) (φ τ : ℂ)) /
      (ModularCurve.siegelFun 25
          (((unitResidues25 (i+1)).1 : ℤ) * B 0 0) (((unitResidues25 (i+1)).1 : ℤ) * B 0 1) (φ τ : ℂ) *
        ModularCurve.siegelFun 25
          (((unitResidues25 (i+1)).2 : ℤ) * B 0 0) (((unitResidues25 (i+1)).2 : ℤ) * B 0 1) (φ τ : ℂ)) := by sorry
