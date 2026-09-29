-- Prove2me | Theorems.Thm_ModularCurve_siegelFun_specialLinearGroup_smul
-- name    : ModularCurve.siegelFun_specialLinearGroup_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/920cb411-3cec-57ef-8fb7-e08f125a62f6
-- title:
--   Transformation of Siegel functions under SL₂(ℤ)
-- statement:
--   Let $N$ be a natural number and let $\alpha$ be an element of $\mathrm{SL}_2(\mathbb{Z})$, i.e. of `Matrix.SpecialLinearGroup (Fin 2) ℤ`. Here, for integers $r,s$ and a complex number $z$, the Siegel function $\mathrm{siegelFun}\,N\,r\,s\,z$ is defined as the product $$-e^{\pi i s (r-N)/N^{2}}\; e^{\pi i ((r/N)^{2}-r/N+1/6)z}\;\bigl(1-w\bigr)\prod_{n\ge 0}\bigl(1-q^{\,n+1}w\bigr)\bigl(1-q^{\,n+1}w^{-1}\bigr),$$ where $q=e^{2\pi i z}$ and $w=e^{2\pi i (rz+s)/N}$, the infinite product being the unconditional `tprod` over $n:\mathbb{N}$. The assertion is the existence of a complex number $\mu$, depending only on $N$ and $\alpha$, with $\mu^{12}=1$, such that for all integers $r,s$ and every point $\tau$ of the upper half-plane one has $$\mathrm{siegelFun}\,N\,r\,s\,(\alpha\cdot\tau)=\mu\,\cdot\,\mathrm{siegelFun}\,N\,(r\alpha_{00}+s\alpha_{10})\,(r\alpha_{01}+s\alpha_{11})\,\tau,$$ both sides being evaluated at the complex numbers underlying $\alpha\cdot\tau$ and $\tau$, where $\alpha\cdot\tau$ is the Möbius action on the upper half-plane. Thus the index vector $(r,s)$ is multiplied on the right by the matrix $\alpha$, without reduction modulo $N$.
--
--   This is the classical transformation law of the Siegel functions under the action of $\mathrm{SL}_2(\mathbb{Z})$, with the twelfth root of unity $\mu$ obtained as a single constant uniform in the index $(r,s)$ and the point $\tau$. It is used to show that suitable products of powers of Siegel functions are invariant, as in [`ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul`](thm.html#ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_siegelFun_specialLinearGroup_smul.lean

import Definitions.Def_ModularCurve_SiegelFunction
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.siegelFun_specialLinearGroup_smul (N : ℕ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * siegelFun N (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ) := by sorry
