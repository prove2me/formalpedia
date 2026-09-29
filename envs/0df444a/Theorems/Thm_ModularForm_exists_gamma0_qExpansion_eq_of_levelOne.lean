-- Prove2me | Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
-- name    : ModularForm.exists_gamma0_qExpansion_eq_of_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/de6d7e36-aff6-5cb4-ae4c-3871257781e3
-- title:
--   A level-one form is a form for Γ₀(N)
-- statement:
--   Let $N$ be a natural number that is nonzero, let $k$ be an integer, and let $F$ be a modular form of weight $k$ for the subgroup $\mathcal{SL}$ of $\mathrm{GL}(2,\mathbb{R})$, i.e. for the image of $\mathrm{SL}(2,\mathbb{Z})$ under the canonical map into $\mathrm{GL}(2,\mathbb{R})$ (the level-one case). The assertion is that there exists a modular form $G$ of the same weight $k$ for the congruence subgroup $\Gamma_0(N)$, in Mathlib's sense `CongruenceSubgroup.Gamma0 N`, whose underlying function $\mathbb{H}\to\mathbb{C}$ is equal to that of $F$. Thus the conclusion is an equality of functions on the upper half-plane, not merely an agreement of $q$-expansions as the name might suggest; it says that an $\mathrm{SL}(2,\mathbb{Z})$-form, regarded as a holomorphic function on $\mathbb{H}$, is in the image of the set of $\Gamma_0(N)$-forms under passage to the underlying function. No hypothesis relating $N$ to $k$ or to $F$ is imposed beyond $N \neq 0$.
--
--   This is the restriction (trivial degeneracy) map from level $1$ to level $N$, stated existentially so that subsequent statements never have to name a restriction operator; it lets level-one forms such as $E_6^2$ and $E_4^2E_6$ be fed into statements formulated for $\Gamma_0(N)$. It is used by the statements on $q$-expansion coefficients of cusp forms at various levels, in particular those comparing Atkin–Lehner and Hecke operators with integrality hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.lean

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_gamma0_qExpansion_eq_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by sorry
