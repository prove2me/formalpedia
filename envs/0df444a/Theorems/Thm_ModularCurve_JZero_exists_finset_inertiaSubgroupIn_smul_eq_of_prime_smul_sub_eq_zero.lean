-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_finset_inertiaSubgroupIn_smul_eq_of_prime_smul_sub_eq_zero
-- name    : ModularCurve.JZero.exists_finset_inertiaSubgroupIn_smul_eq_of_prime_smul_sub_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/27be46bd-7d02-52b0-82ee-326f40f63613
-- title:
--   Inertia fixes prime-to-ℓ Kummer classes on J₀(N)
-- statement:
--   Let $N$ be a nonzero natural number. The assertion is that there is a finite set $S$ of natural numbers with the following property. Let $\ell$ be a prime with $\ell \notin S$, and let $A$ be a valuation subring of a fixed algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ which lies over $\ell$, meaning that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$. Let $\sigma$ be an element of the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, that is, of the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup into the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. Let $p$ be a prime different from $\ell$, and let $y$ be an element of `JZero N`, the group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$, i.e. degree-zero divisors modulo principal divisors, with its action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Then $p \cdot (\sigma \cdot y - y) = 0$ implies $\sigma \cdot y = y$.
--
--   This is the good-reduction (Néron–Ogg–Shafarevich) input for the Jacobian of the modular curve of level $N$: away from a finite set of primes, inertia acts trivially on classes whose $\sigma$-difference is killed by a prime other than the residue characteristic, which is exactly the statement that the Kummer classes attached to inertia-invariant points are unramified outside that set. It is used in the proof that the image of multiplication by $2$ has finite index in the invariants of `JZero N`, a step of the weak Mordell–Weil argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_finset_inertiaSubgroupIn_smul_eq_of_prime_smul_sub_eq_zero.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.exists_finset_inertiaSubgroupIn_smul_eq_of_prime_smul_sub_eq_zero (N : ℕ) [NeZero N] :
    ∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ p : ℕ, p.Prime → p ≠ ℓ →
          ∀ y : JZero N, p • (σ • y - y) = 0 → σ • y = y := by sorry
