-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsion_jZero_eq_pow_finrank_periodLattice
-- name    : ModularCurve.natCard_torsion_jZero_eq_pow_finrank_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/7f09d008-6e0c-5d32-ad50-674d153c0e7f
-- title:
--   n-torsion of J₀(N) over ℚ̄ has order n^{rank Λ_N}
-- statement:
--   Let $N$ be a nonzero natural number and $n$ a nonzero natural number. Consider the field $\overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$ used in Mathlib) and the intermediate field [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111) of $\overline{\mathbb Q}((q))$, namely the subfield generated over $\overline{\mathbb Q}$ by the coefficientwise image in $\overline{\mathbb Q}((q))$ of [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305), the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the $q$-expansions `divisorExpansions N`. For this extension, `Pic0` is the quotient of the group of finitely supported $\mathbb Z$-valued functions on the places of the extension that lie in the kernel of the degree map, by the subgroup of those that are the divisor of a nonzero element of the field; `Pic0.torsion … n` is the subgroup of classes killed by $n$, i.e. the $\mathbb Z$-torsion submodule `Submodule.torsionBy ℤ _ (n : ℤ)`. Let $\Lambda_N =$ [`ModularCurve.periodLattice N`](def/ModularCurve_PeriodLattice.html#L102) be the $\mathbb Z$-submodule of the $\mathbb C$-dual of $\mathrm{CuspForm}(\Gamma_0(N),2)$ spanned by the periods `period N γ` $=$ `periodAlong N I (γ • I)` for $\gamma \in \Gamma_0(N)$. The assertion is that the number of elements of the $n$-torsion of this degree-zero divisor class group equals $n$ raised to the $\mathbb Z$-rank of $\Lambda_N$.
--
--   This is the torsion count for the Jacobian $J_0(N)$ in the form $\#J_0(N)(\overline{\mathbb Q})[n] = n^{\operatorname{rank}_{\mathbb Z}\Lambda_N}$, stated in terms of the rank of the period lattice rather than the genus of $X_0(N)$, so that no genus bookkeeping enters. It is the input used downstream for finiteness and freeness of Tate modules of $J_0(N)$, for Hecke eigenform support statements, and for the local analysis of $J_0(N)$ at primes of good and bad reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsion_jZero_eq_pow_finrank_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.natCard_torsion_jZero_eq_pow_finrank_periodLattice (N : ℕ) [NeZero N]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
      = n ^ Module.finrank ℤ (ModularCurve.periodLattice N) := by sorry
