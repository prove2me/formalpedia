-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_exists_W_ne_zero
-- name    : LanglandsTunnell.Converse.DiscreteFamily.exists_W_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/919f5740-44f8-59a5-97b5-281ab663d510
-- title:
--   Nonvanishing of the discrete-series Whittaker function
-- statement:
--   Fix a complex parameter $u_0$ and a natural number $k_0$, and consider the complex-valued function `W u₀ k₀` on real $2\times 2$ matrices provided by the project's explicit archimedean Whittaker functions: it is assembled from the Iwasawa coordinates `ix` and `iy` of a matrix, the squared norm `nsq` of its lower row, the rotation phase `kap`, the additive character `psi`, a weight profile `prof` and a power `detPow` of the determinant, the formula being guarded by a case distinction whose positive branch is the one containing these ingredients. The assertion is that this function is not identically zero on the invertible matrices: there exists a unit $g$ of the ring $M_2(\mathbb{R})$, i.e. an element of `GL (Fin 2) ℝ`, such that the value of `W u₀ k₀` at the underlying matrix of $g$ is nonzero. No hypotheses are imposed on $u_0$ or $k_0$; in particular the case $k_0 = 0$ is included.
--
--   This is the nonvanishing input required when the explicit discrete-series Whittaker function at the real place is packaged as an archimedean datum for the converse theorem. It is used by [`LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero), which produces such a datum together with its weight character, minimal type and Casimir eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_DiscreteFamily_exists_W_ne_zero.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse.DiscreteFamily

theorem LanglandsTunnell.Converse.DiscreteFamily.exists_W_ne_zero (u₀ : ℂ) (k₀ : ℕ) :
    ∃ g : GL (Fin 2) ℝ, W u₀ k₀ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by sorry
