-- Prove2me | Theorems.Thm_N25_GammaH25GL_isArithmetic
-- name    : N25.GammaH25GL_isArithmetic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:01.680311+00:00
-- url     : https://prove2.me/theorems/ab9512ad-6865-4723-bf67-5aeb462bb9d0
-- title:
--   $\Gamma_H(25)$ is an arithmetic subgroup of $\mathrm{GL}_2(\mathbf R)$
-- statement:
--   Let $H=\langle7\rangle\subset(\mathbf Z/25\mathbf Z)^\times$, and view the congruence subgroup $\Gamma_H(25)$ inside $\mathrm{GL}_2(\mathbf R)$ through the standard inclusion of integral matrices. Then
--
--   $$\Gamma_H(25)\text{ is arithmetic}.$$
--
--   This provides the arithmetic-group hypothesis required by the analytic modular-function machinery.
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

theorem N25.GammaH25GL_isArithmetic : GammaH25GL.IsArithmetic := by sorry
