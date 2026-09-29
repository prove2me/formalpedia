-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_isRepOf_forall_apply_cuspInftyBar_le
-- name    : ModularCurve.JZero.exists_isRepOf_forall_apply_cuspInftyBar_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/543cecf7-5c06-56f3-a05d-af8e97a5ae78
-- title:
--   Existence of a cusp-maximal representative of a class in J₀(N)
-- statement:
--   Fix $N \geq 1$, a subfield $K$ of $\overline{\mathbb{Q}}$ (an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$) that is finite-dimensional over $\mathbb{Q}$, and a natural number $n$. Write $\bar F_N$ for `modularFunctionFieldBar N`, the compositum over $\overline{\mathbb{Q}}$ of the images of the $q$-expansion field `modularFunctionFieldFull N` inside $\overline{\mathbb{Q}}((q))$, and let $\mathrm{JZero}\,N$ be its degree-zero divisor class group $\mathrm{Pic}^0$; divisors are finitely supported $\mathbb{Z}$-valued functions on the places of $\bar F_N$ over $\overline{\mathbb{Q}}$, and $\overline{\infty} =$ `cuspInftyBar N` is the $q$-adic place. Let $c$ be a class in $\mathrm{JZero}\,N$ fixed by the subgroup of $\overline{\mathbb{Q}}$-automorphisms over $\mathbb{Q}$ fixing $K$ pointwise, acting through `arithmeticGalois`. Call $D$ a representative of $c$ of degree $n$ over $K$ (the relation `JZero.IsRepOf N K n c D`) when $D$ is effective, $D = E + n\,\overline{\infty}$ for some divisor $E$ of degree $0$ whose class is $c$, and $D$ is fixed by every element of the fixing subgroup of $K$ acting through `arithmeticGalois`. Assuming at least one such $D$ exists, the theorem produces a representative $D'$ of $c$ of degree $n$ over $K$ such that the Riemann–Roch space of $D' - D'(\overline{\infty})\,\overline{\infty} - \overline{\infty}$ (that is, of the divisor obtained from $D'$ by erasing its value at $\overline{\infty}$ and then subtracting one copy of $\overline{\infty}$), namely the $\overline{\mathbb{Q}}$-subspace of $f \in \bar F_N$ whose valuation at each place $v$ is at most $\exp$ of the coefficient of that divisor at $v$, is zero, and such that $D(\overline{\infty}) \leq D'(\overline{\infty})$ for every representative $D$ of $c$ of degree $n$ over $K$.
--
--   This is the existence of the cusp-maximal representative of a $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$-invariant effective divisor class of the form $c + n\,\overline{\infty}$ on $X_0(N)$: the vanishing of the Riemann–Roch space of the off-cusp part minus $\overline{\infty}$ and the maximality of the multiplicity at the cusp are the two readings of the same extremality. It is used in the construction of the height form on $J_0(N)$, through [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_isRepOf_forall_apply_cuspInftyBar_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_isRepOf_forall_apply_cuspInftyBar_le (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (n : ℕ)
    (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
    (hc : ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K n c D) :
    ∃ D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K n c D' ∧
      riemannRochSpace (D'.erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ ∧
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K n c D →
        D (cuspInftyBar N) ≤ D' (cuspInftyBar N) := by sorry
