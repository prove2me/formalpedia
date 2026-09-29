-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
-- name    : IsDiscreteValuationRing.exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/567a8c0d-de9c-5d92-9565-6072cffd2be9
-- title:
--   Total ramification criterion over a discrete valuation ring
-- statement:
--   Let $O$ be a discrete valuation ring which is a domain, $F$ a field that is a fraction field of $O$, and $E$ a field extension of $F$ which is also an $O$-algebra compatibly (an $O$–$F$–$E$ scalar tower), with $E$ finite-dimensional over $F$. Assume that $R = \mathrm{integralClosure}\,O\,E$, the integral closure of $O$ in $E$, is a Dedekind domain, is finite as an $O$-module, and has $E$ as fraction field. Write $\mathfrak m = \mathrm{maximalIdeal}\,O$. Let $n$ be a natural number with $[E:F] \le n$, and suppose that for every non-zero prime ideal $\mathfrak P$ of $R$ lying over $\mathfrak m$ (i.e. with $\mathfrak m = \mathfrak P \cap O$ in the `LiesOver` sense) one has $n \mid e(\mathfrak P \mid \mathfrak m)$, the ramification index in the primed Mathlib form `ramificationIdx'`. Then there exists a prime ideal $\mathfrak P$ of $R$ with $\mathfrak P \neq \bot$ such that the set of primes of $R$ over $\mathfrak m$ is exactly $\{\mathfrak P\}$, $e(\mathfrak P \mid \mathfrak m) = n$, the residue degree $f(\mathfrak P \mid \mathfrak m)$ (as `inertiaDeg'`) equals $1$, and $[E:F] = n$.
--
--   This is the standard criterion identifying a totally ramified extension of a discrete valuation ring: a divisibility condition on ramification indices, together with the degree bound $[E:F] \le n$, forces a single prime above $\mathfrak m$ with $e = n$, $f = 1$ and $[E:F] = n$. It is used in the treatment of valuation subrings and Kummer-type extensions, where a unique prime of known ramification is needed to compare valuations of elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Type*) [Field F] [Algebra O F] [IsFractionRing O F]
    (E : Type*) [Field E] [Algebra F E] [Algebra O E] [IsScalarTower O F E]
    [FiniteDimensional F E]
    [IsDedekindDomain ↥(integralClosure O E)] [Module.Finite O ↥(integralClosure O E)]
    [IsFractionRing ↥(integralClosure O E) E]
    (n : ℕ) (hn : Module.finrank F E ≤ n)
    (hdvd : ∀ (𝔓 : Ideal ↥(integralClosure O E)) [𝔓.IsPrime], 𝔓 ≠ ⊥ →
      𝔓.LiesOver (IsLocalRing.maximalIdeal O) → n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓) :
    ∃ (𝔓 : Ideal ↥(integralClosure O E)), 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O E) = {𝔓} ∧
      (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = n ∧
      (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 = 1 ∧
      Module.finrank F E = n := by sorry
