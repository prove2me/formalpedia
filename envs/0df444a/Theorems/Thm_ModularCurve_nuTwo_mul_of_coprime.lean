-- Prove2me | Theorems.Thm_ModularCurve_nuTwo_mul_of_coprime
-- name    : ModularCurve.nuTwo_mul_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/879067dc-585f-5669-bb14-86e09c81894f
-- title:
--   Multiplicativity of ν₂ at coprime arguments
-- statement:
--   For natural numbers $M$ and $N$ with $\gcd(M,N)=1$, the quantity $\nu_2(MN)$ equals $\nu_2(M)\,\nu_2(N)$, where for a natural number $N$ the value $\nu_2(N)$ is defined as the cardinality (in the sense of `Nat.card`) of the subtype of elements $x$ of $\mathbb{Z}/N\mathbb{Z}$ satisfying $x^2 + 1 = 0$. Thus the assertion is purely a counting statement about square roots of $-1$ in residue rings: the number of solutions of $x^2+1=0$ in $\mathbb{Z}/MN\mathbb{Z}$ is the product of the numbers of solutions in $\mathbb{Z}/M\mathbb{Z}$ and in $\mathbb{Z}/N\mathbb{Z}$, under no hypothesis on $M$ and $N$ beyond coprimality (in particular the degenerate cases where $M$ or $N$ is $0$ or $1$ are included, with `Nat.card` returning $0$ for infinite types).
--
--   Classically $\nu_2(N)$ counts the elliptic points of order $2$ on the modular curve attached to $\Gamma_0(N)$, and its multiplicativity is the first step in reducing the genus formula for $X_0(N)$ to prime powers. Within the development it is used by [`ModularCurve.genusFormula_mul_expand`](thm.html#ModularCurve.genusFormula_mul_expand).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nuTwo_mul_of_coprime.lean

import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.nuTwo_mul_of_coprime {M N : ℕ} (h : Nat.Coprime M N) : nuTwo (M * N) = nuTwo M * nuTwo N := by sorry
