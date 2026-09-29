-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
-- name    : LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/96d06228-b2ed-5113-82c9-5d79e7b60012
-- title:
--   Lower unipotent support of a spherical Whittaker function
-- statement:
--   Let $v$ be a height one prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$, valuation ring $\mathcal{O}_v = \{x : \mathrm{v}(x) \le 1\}$, and let $\psi_v$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$ for which there is some $x$ with $\mathrm{v}(x) \le \exp(1)$ and $\psi_v(x) \ne 1$. Let $W \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be a function satisfying the $\psi_v$-Whittaker transformation law, i.e. $W(n(x,y,z)\,g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $n(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$; assume further that $W$ is invariant under right translation by the subgroup of those $k \in \mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries, and all of whose entries of $k^{-1}$, have valuation at most $1$. Let $a \in \mathbb{Q}_v^{\times}$ and $x \in \mathbb{Q}_v$, and write $\iota$ for the homomorphism $\mathrm{GL}_2 \to \mathrm{GL}_3$ placing a matrix in the upper left block with $1$ in the $(3,3)$ entry. If $W\bigl(\iota(\mathrm{diag}(a,1))\cdot u(x)\bigr) \ne 0$, where $u(x)$ is the lower triangular unipotent matrix with $x$ in position $(2,1)$ and $1$ in position $(3,3)$, then $x \in \mathcal{O}_v$.
--
--   This is the support statement for the inner integrand of the local Rankin–Selberg zeta integral for $\mathrm{GL}_3 \times \mathrm{GL}_1$: a right spherically invariant Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ vanishes at $\mathrm{diag}(a,1,1)u(x)$ unless $x$ is a $v$-adic integer, so that the integral over $\mathbb{Q}_v$ in the $(2,1)$ variable reduces to an integral over $\mathcal{O}_v$. It is used in the computation of the local zeta integral at a place where the relevant Whittaker function is spherical, towards the Euler product for the $\mathrm{GL}_3$ zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (hW0 : W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x) ≠ 0) :
    x ∈ v.adicCompletionIntegers ℚ := by sorry
