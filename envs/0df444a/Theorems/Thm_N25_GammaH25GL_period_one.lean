-- Prove2me | Theorems.Thm_N25_GammaH25GL_period_one
-- name    : N25.GammaH25GL_period_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:37.289191+00:00
-- url     : https://prove2.me/theorems/9fe85a2d-f57a-4796-883a-ad58b71c362a
-- title:
--   Translation by one is a strict period of $\Gamma_H(25)$
-- statement:
--   Let $\Gamma_H(25)\subset\mathrm{GL}_2(\mathbf R)$ be the level-$25$ congruence subgroup attached to $H=\langle7\rangle$. Its set of strict real periods contains $1$:
--
--   $$1\in\operatorname{Per}_{\mathrm{strict}}(\Gamma_H(25)).$$
--
--   This records the unit translation needed for Fourier and $q$-expansion constructions.
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

theorem N25.GammaH25GL_period_one : (1 : ℝ) ∈ GammaH25GL.strictPeriods := by sorry
