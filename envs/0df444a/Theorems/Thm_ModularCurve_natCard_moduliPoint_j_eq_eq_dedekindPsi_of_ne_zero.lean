-- Prove2me | Theorems.Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
-- name    : ModularCurve.natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/300b7dc3-8bfa-5c31-8cfc-99ac8b845c61
-- title:
--   Generic j-fibres of Γ₀(N)-moduli have ψ(N) points
-- statement:
--   Fix a natural number $N$ with $N \neq 0$ and an algebraically closed field $L$ with decidable equality, and assume that $N$, $2$ and $3$ are all nonzero in $L$. Let $j_0 \in L$ satisfy $j_0 \neq 0$ and $j_0 \neq 1728$. The set $\mathrm{ModuliPoint}\ N\ L$ is the quotient of the type of triples consisting of a Weierstrass curve $W$ over $L$, a proof that $W$ is elliptic, and a point $P$ of the affine model of $W$ whose additive order is exactly $N$, by the relation `Gamma0Pair.Step`: two such triples $(W,P)$, $(W',P')$ are related when there is a Weierstrass variable change $\gamma$ with $\gamma \bullet W = W'$ and a natural number $k$ coprime to $N$ with $P'$ equal (over the identification of the two curves) to $k$ times the image of $P$ under $\gamma$. The theorem asserts that the fibre over $j_0$ of the $j$-invariant map on this quotient is finite of cardinality $\psi(N)$, where the Dedekind psi function is given here as $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d = N\prod_{p \mid N}(1 + p^{-1})$.
--
--   This is the count of $\Gamma_0(N)$-structures above a fixed $j$-invariant away from the two exceptional values $j = 0, 1728$, i.e. the assertion that the forgetful map $Y_0(N) \to Y(1)$ has all its generic fibres of size $\psi(N) = [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]$, the points of the fibre being indexed by the cyclic subgroups of order $N$ of $W(L)$ since the automorphism group of a curve with $j \neq 0, 1728$ in characteristic $\neq 2, 3$ is $\{\pm 1\}$, which acts trivially on subgroups. It feeds the counting arguments behind [`ModularCurve.card_eq_ssCountFormula_of_ssPlaces`](thm.html#ModularCurve.card_eq_ssCountFormula_of_ssPlaces) and [`ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (hN : (N : L) ≠ 0) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (j₀ : L) (h0 : j₀ ≠ 0) (h1728 : j₀ ≠ 1728) :
    Nat.card {x : ModuliPoint N L // ModuliPoint.j x = j₀} = dedekindPsi N := by sorry
