-- Prove2me | Theorems.Thm_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem
-- name    : MvPowerSeries.module_finite_quotient_of_forall_X_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/01779660-c737-5ec3-bbc3-3e345c08e9f5
-- title:
--   Finiteness of a power-series quotient killing powers of the variables
-- statement:
--   Let $\sigma$ be a finite type of indeterminates and $R$ a commutative ring, and let $I$ be an ideal of the multivariate formal power series ring $\mathrm{MvPowerSeries}\,\sigma\,R = R[\![x_s : s \in \sigma]\!]$. Suppose there is a natural number $N$ such that for every $s : \sigma$ the $N$-th power $x_s^N$ of the corresponding variable `MvPowerSeries.X s` belongs to $I$. The assertion is then that the quotient ring $R[\![x_s : s \in \sigma]\!] \,/\, I$ is a finite $R$-module, i.e. `Module.Finite R` holds for it, the $R$-module structure being the one coming from the canonical ring map $R \to R[\![x_s : s \in \sigma]\!]$ followed by the quotient map: the quotient is generated as an $R$-module by finitely many elements. No Noetherian or flatness hypothesis on $R$ is imposed, and the degenerate cases are included: for $N = 0$ the hypothesis forces $1 \in I$ and the quotient is the zero module, and for $\sigma$ empty the quotient is a quotient of $R$ itself.
--
--   This is the standard finiteness statement for truncated power series: an ideal containing a power of each coordinate cuts out an infinitesimal neighbourhood of the origin that is module-finite over the base. It is used in the analysis of formal isomorphisms and kernels of isogenies attached to fake elliptic curves, where the quotient by such an ideal must be recognised as a finite $R$-module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPowerSeries.module_finite_quotient_of_forall_X_pow_mem
    {σ : Type} [Fintype σ] {R : Type} [CommRing R] (I : Ideal (MvPowerSeries σ R)) (N : ℕ)
    (hI : ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈ I) :
    Module.Finite R (MvPowerSeries σ R ⧸ I) := by sorry
