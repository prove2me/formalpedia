-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
-- name    : ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/4bb6612b-c26e-5d42-8b4a-afd082885716
-- title:
--   Φ_N(j(Λ),j(Λ'))=0 for cyclic sublattices of index N
-- statement:
--   Let $N$ be a nonzero natural number and let `data` be a [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215), that is, a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals the Dedekind function value $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which is annihilated by the substitution sending the coefficient variable to the $q$-expansion of $j$ and $Y$ to the series `jqN N` in Laurent series over $\mathbb{Q}$. Let $L$ and $L'$ be period pairs, i.e. lattices in $\mathbb{C}$ given by a pair of periods, such that the lattice of $L'$ is contained, as a subset of $\mathbb{C}$, in the lattice of $L$, such that the index of the additive subgroup of $L$'s lattice cut out by $L'$'s lattice equals $N$, and such that the corresponding quotient group is cyclic. Then, writing $j(M) = 1728\,g_2(M)^3/(g_2(M)^3 - 27 g_3(M)^2)$ for the lattice invariant `jLattice`, the polynomial obtained from $\Phi$ by evaluating each coefficient in $\mathbb{C}$ at $j(L)$ (along $\mathbb{Z} \to \mathbb{C}$) vanishes at $j(L')$; that is, $\Phi\bigl(j(L), j(L')\bigr) = 0$.
--
--   This is the analytic description of $Y_0(N)(\mathbb{C})$ as the zero locus of the modular polynomial: a pair of $j$-invariants of lattices related by a cyclic sublattice inclusion of index $N$ is a root of $\Phi_N$. It feeds the transfer of the modular equation to elliptic curves, being used for the statements about $j$-invariants of curves linked by an isogeny whose kernel is cyclic of the appropriate order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0 := by sorry
