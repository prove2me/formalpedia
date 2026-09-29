-- Prove2me | Theorems.Thm_ModularCurve_CuspSpace_exists_normalForm
-- name    : ModularCurve.CuspSpace.exists_normalForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/cb606138-7b7a-5f4f-b98f-8a06b99ca877
-- title:
--   Normal form for a cusp of Γ₀(N)
-- statement:
--   Let $N$ be a non-zero natural number and let $x$ be a point of [`ModularCurve.CuspSpace N`](def/ModularCurve_CuspSpace.html#L103), that is, an element of the orbit space of $\mathbb{P}^1(\mathbb{Q})$ (realised as `OnePoint ℚ`) under `Gamma0Q N`, the image of $\Gamma_0(N)$ in $\mathrm{GL}_2(\mathbb{Q})$ under `mapGL ℚ`. Write $d =$ `cuspDenom N x` for the natural number attached to the orbit of $x$ by the orbit-invariant function sending $\infty$ to $N$ and a rational $q$ to $\gcd(\mathrm{den}\, q, N)$. The assertion is that there exists an integer $a$ such that $a$ and $d$ are coprime in $\mathbb{Z}$ in the Bézout sense (some $\mathbb{Z}$-combination of $a$ and $d$ equals $1$) and such that $x$ is the orbit [`ModularCurve.CuspSpace.mk N`](def/ModularCurve_CuspSpace.html#L107) of the point [`ModularCurve.ratPoint a d`](def/ModularCurve_CuspSpace.html#L11), which is $\infty$ if $d = 0$ and the image of $a/d \in \mathbb{Q}$ in $\mathbb{P}^1(\mathbb{Q})$ otherwise. Thus every cusp of $\Gamma_0(N)$ is represented by $a/d$ with $d$ its denominator invariant and $a$ coprime to $d$.
--
--   This is the existence (surjectivity) half of the classical normal-form description of the cusps of $\Gamma_0(N)$, in which a cusp is presented as $a/d$ with $d \mid N$ the denominator invariant and $\gcd(a,d) = 1$. It is used in the classification of `CuspSpace N` and in the verification that a Hecke operator acts as expected on parabolic homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CuspSpace_exists_normalForm.lean

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint

theorem ModularCurve.CuspSpace.exists_normalForm {N : ℕ} (hN : N ≠ 0) (x : ModularCurve.CuspSpace N) :
    ∃ a : ℤ, IsCoprime a (ModularCurve.CuspSpace.cuspDenom N x : ℤ) ∧
      x = ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint a (ModularCurve.CuspSpace.cuspDenom N x)) := by sorry
