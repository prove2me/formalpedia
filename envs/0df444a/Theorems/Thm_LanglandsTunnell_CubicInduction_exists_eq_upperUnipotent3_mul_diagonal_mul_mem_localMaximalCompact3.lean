-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
-- name    : LanglandsTunnell.CubicInduction.exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d7e2206c-96b9-5a7b-9d01-91428c6b9ca5
-- title:
--   Iwasawa decomposition NTK for GL₃ over a completion of ℚ
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ and let $g$ be an element of `LocalGL3 v`, the group $\mathrm{GL}_3$ over the $v$-adic completion $F_v$ of $\mathbb{Q}$. Then there exist elements $x,y,z\in F_v$, an element $t$ of $\mathrm{GL}_3(F_v)$, a triple $d\colon \mathrm{Fin}\,3\to F_v$ and an element $k$ of the subgroup `localMaximalCompact3` of $\mathrm{GL}_3(F_v)$ — that is, a $k$ such that every entry of the matrix of $k$ and every entry of the matrix of $k^{-1}$ has valuation $\le 1$ for the valuation of $F_v$ — such that the underlying matrix of $t$ is the diagonal matrix $\mathrm{diagonal}\,d$ and $g = \mathrm{upperUnipotent3}(x,y,z)\cdot t\cdot k$, where $\mathrm{upperUnipotent3}(x,y,z)$ is the unit of $\mathrm{GL}_3(F_v)$ with matrix $!![1,x,z;0,1,y;0,0,1]$ (its inverse being $!![1,-x,xy-z;0,1,-y;0,0,1]$). No normalisation of $d$ is asserted: in particular no inequality between the valuations of the diagonal entries $d\,0, d\,1, d\,2$ is claimed, only that they form an invertible diagonal matrix.
--
--   This is the Iwasawa decomposition $G = NTK$ for $\mathrm{GL}_3$ over a non-archimedean completion of $\mathbb{Q}$, with $N$ the upper unipotent subgroup, $T$ the diagonal torus and $K$ the maximal compact subgroup of matrices integral together with their inverses. It underlies the local computations with Whittaker functions and local zeta integrals in the cubic-induction part of the Langlands–Tunnell input, where integrals over $\mathrm{GL}_3(F_v)$ are reduced to integrals over the torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    ∃ (x y z : v.adicCompletion ℚ) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      ∃ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
        (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d ∧
          g = upperUnipotent3 x y z * t * k := by sorry
