-- Prove2me | Theorems.Thm_NumberField_tsum_split_degOne_le
-- name    : NumberField.tsum_split_degOne_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/d79db4c3-99ac-5f3f-93cf-d972e99948ba
-- title:
--   Split primes bounded by q⁻¹logζ_M(s)
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an algebra over $K$ which is Galois over $K$, and let $q$ be a prime natural number with $3 \le q$ such that $[M:K] = q$ as the rank of $M$ as a $K$-module. Then there exists a real constant $C$ with the following property: for every real $s > 1$, the sum, over the set of those ideals $\mathfrak l$ of $\mathcal O_K$ that are maximal, have prime absolute norm $\mathrm{N}(\mathfrak l)$, and admit exactly $[M:K]$ primes of $\mathcal O_M$ lying over them, of the terms $\mathrm{N}(\mathfrak l)^{-s}$ (the sum being the unconditional infinite sum over that index set, with $\mathrm{N}(\mathfrak l)$ viewed as a real number) is at most $$q^{-1}\log\bigl\lVert \zeta_M(s)\bigr\rVert + C,$$ where $\zeta_M$ is the Dedekind zeta function of $M$ evaluated at the real point $s$ and $\lVert\cdot\rVert$ is its absolute value. Thus the conditions defining a "split prime" here are exactly: maximality, degree one over $\mathbb Q$ (prime norm), and complete splitting in $M$.
--
--   This is the density half of the class-field-theory-free argument that the degree-one primes of $K$ which do not split completely in a prime-degree Galois extension $M/K$ generate the class group: the split primes contribute at most $1/q \le 1/3$ of the polar part of $\log\zeta_M(s)$ as $s \to 1^{+}$. It is used by [`NumberField.classGroup_eq_closure_nonSplit_degOne`](thm.html#NumberField.classGroup_eq_closure_nonSplit_degOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_tsum_split_degOne_le.lean

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Definitions.Def_NumberField_IsSplitPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace NumberField
open scoped NumberField nonZeroDivisors
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

theorem tsum_split_degOne_le (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q)
    (hdeg : Module.finrank K M = q) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      ∑' 𝔩 : {I : Ideal (𝓞 K) // IsSplitPrime K M I},
          ((Ideal.absNorm (𝔩 : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹
        ≤ (q : ℝ)⁻¹ * Real.log ‖dedekindZeta M s‖ + C := by sorry
