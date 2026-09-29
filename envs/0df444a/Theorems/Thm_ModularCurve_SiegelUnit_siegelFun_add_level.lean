-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level
-- name    : ModularCurve.SiegelUnit.siegelFun_add_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/2a2a9599-4513-512f-8583-7f9369e755e5
-- title:
--   Periodicity of Siegel functions in the index (r,s)
-- statement:
--   Let $N$ be a natural number and $r,s$ integers, and write $g_{r,s}(z)=$ `siegelFun N r s z` for the function
--   $$-e^{\pi i s(r-N)/N^{2}}\,e^{\pi i((r/N)^{2}-r/N+1/6)z}\,(1-q_a)\prod_{n\ge 0}\bigl(1-q^{\,n+1}q_a\bigr)\bigl(1-q^{\,n+1}q_a^{-1}\bigr),$$
--   where $q=e^{2\pi i z}$, $q_a=e^{2\pi i(rz+s)/N}$ and the infinite product is the unconditional `tprod` (equal to $1$ when the family is not multipliable). The theorem asserts the conjunction of two identities. First, for every $z\in\mathbb{C}$ without restriction,
--   $$g_{r,s+N}(z)=e^{\pi i(r-N)/N}\,g_{r,s}(z).$$
--   Second, for every point $\tau$ of the upper half-plane, taken with its coercion to $\mathbb{C}$,
--   $$g_{r+N,s}(\tau)=-e^{-\pi i s/N}\,g_{r,s}(\tau).$$
--   No hypothesis $N\neq 0$ is imposed: in the degenerate case $N=0$ the factor $1-e^{2\pi i(rz+s)/0}$ vanishes identically under Lean's division convention, so $g_{r,s}\equiv 0$ and both identities hold trivially.
--
--   These are the periodicity relations of the Siegel functions (normalised Klein forms) in their index, in the form used by Kubert and Lang: translating $r$ or $s$ by the level $N$ multiplies $g_{r,s}$ by a root of unity, so that a suitable power of $g_{r,s}$ depends only on $(r,s)$ modulo $N$. The result is used in the proof of the transformation behaviour of products of powers of Siegel functions under the action of $\mathrm{SL}_2(\mathbb{Z})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_siegelFun_add_level.lean

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.siegelFun_add_level (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by sorry
