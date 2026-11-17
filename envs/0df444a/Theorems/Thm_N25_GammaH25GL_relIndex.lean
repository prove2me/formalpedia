-- Prove2me | Theorems.Thm_N25_GammaH25GL_relIndex
-- name    : N25.GammaH25GL_relIndex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:45.931526+00:00
-- url     : https://prove2.me/theorems/3abcb5c9-2ca6-49c9-a7c4-7896d8cc8ebd
-- title:
--   The relative index of $\Gamma_H(25)$ is $150$
-- statement:
--   Let $\Gamma_H(25)$ be viewed as a subgroup of $\mathrm{GL}_2(\mathbf R)$, and let $\mathcal S\mathcal L$ denote the standard real image of $\mathrm{SL}_2(\mathbf Z)$. Then the relative index is
--
--   $$[\mathcal S\mathcal L:\Gamma_H(25)]=150.$$
--
--   This gives the finite-index datum used in the analytic and modular-unit calculations.
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

theorem N25.GammaH25GL_relIndex : GammaH25GL.relIndex 𝒮ℒ = 150 := by sorry
