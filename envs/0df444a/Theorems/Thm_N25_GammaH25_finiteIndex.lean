-- Prove2me | Theorems.Thm_N25_GammaH25_finiteIndex
-- name    : N25.GammaH25_finiteIndex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:53.698622+00:00
-- url     : https://prove2.me/theorems/09764635-4977-48a1-9a44-d6aa630a2d63
-- title:
--   $\Gamma_H(25)$ has finite index in $\mathrm{SL}_2(\mathbf Z)$
-- statement:
--   Let $H=\langle7\rangle\subset(\mathbf Z/25\mathbf Z)^\times$ and let $\Gamma_H(25)$ be the corresponding subgroup of $\mathrm{SL}_2(\mathbf Z)$. Then its quotient in the ambient modular group is finite:
--
--   $$[\mathrm{SL}_2(\mathbf Z):\Gamma_H(25)]<\infty.$$
--
--   This is the finite-index condition needed to regard the quotient as a modular curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Definitions.Def_N25

set_option autoImplicit false
open scoped MatrixGroups
open Matrix.SpecialLinearGroup
open N25

theorem N25.GammaH25_finiteIndex : N25.Endgame.Γ25.FiniteIndex := by sorry
