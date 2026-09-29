-- Prove2me | Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
-- name    : ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/fb6ad152-fbff-5727-97a8-4508cee47650
-- title:
--   q-expansion of τ↦ F(Nτ) for level-one F
-- statement:
--   Let $N$ be a natural number that is nonzero, let $k$ be an integer, and let $F$ be a modular form of weight $k$ for the subgroup $\mathcal{SL} \le \mathrm{GL}(2,\mathbb{R})$ (the image of $\mathrm{SL}(2,\mathbb{Z})$), acting on the upper half-plane $\mathbb{H}$. Here [`ModularForm.heckeDiagMatrix N`](def/ModularForm_HeckeOperator.html#L21) is, for $N \neq 0$, the element of $\mathrm{GL}(2,\mathbb{R})$ given by the upper triangular matrix $\begin{pmatrix} N & 0 \\ 0 & 1\end{pmatrix}$, whose action on $\mathbb{H}$ is $\tau \mapsto N\tau$; and [`ModularCurve.qExpand ℂ N`](def/ModularCurve_X0.html#L25) is the ring endomorphism of the Laurent series field $\mathbb{C}(\!(q)\!)$ obtained by embedding the exponent group $\mathbb{Z}$ along multiplication by $N$, i.e. the substitution $q \mapsto q^{N}$, which sends the coefficient of index $m$ to the coefficient of index $Nm$ and sets all coefficients of index not divisible by $N$ to zero. The assertion is that the width-one $q$-expansion of the dilated function $\tau \mapsto F(N\tau)$, viewed as a power series and then as a Laurent series, equals the image under this substitution of the width-one $q$-expansion of $F$; in the classical notation, the expansion of $F(N\tau)$ is $\tilde F(q^{N})$.
--
--   This identifies the $q$-expansion of the degeneracy (dilation) image of a level-one form, the basic compatibility between the map $\tau \mapsto N\tau$ on $\mathbb{H}$ and the substitution $q \mapsto q^{N}$ on Laurent expansions. It is used in the analytic study of modular curves and their cusps, for instance in the computations with modular polynomial data and Tate-type expansions that invoke it downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ((qExpansion 1 (fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix N • τ)) : PowerSeries ℂ) : LaurentSeries ℂ) = ModularCurve.qExpand ℂ N ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry
