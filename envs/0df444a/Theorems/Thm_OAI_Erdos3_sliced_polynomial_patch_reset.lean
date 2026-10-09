-- Prove2me | Theorems.Thm_OAI_Erdos3_sliced_polynomial_patch_reset
-- name    : OAI.Erdos3.sliced_polynomial_patch_reset
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T15:17:37.211616+00:00
-- url     : https://prove2.me/theorems/3f08a2f6-a99f-4ac7-b145-576309b7794b
-- title:
--   A polynomial patch correlation yields a long progression on which f averages above b
-- statement:
--   For every natural number $s$ there are a real $C\ge1$ and a natural number $P>0$ such that the following holds. Let $d,N,M,a_0,q_0\in\mathbb N$, $U\in\mathbb R$, $A$ a `PolynomialPatch Unit s d` (a structure bundling $d$ slot weights in $[1,s]$, a polynomial slot form in one real variable and a `PatchKernel d`, a $[0,1]$-valued Lipschitz kernel with Lipschitz constant `kernel.lip`; $A(t)$ denotes its `value`), and $f\colon\mathbb N\to\mathbb R$. Assume $q_0>0$; $a_0+q_0n<N$ for all $n<M$; $f(n)\in[0,1]$ for all $n<N$; $1\le U$; $\log N-U\le\log M$; and $\mathrm{lip}(A)+1\le e^U$. Then for every $b\in[0,1]$, putting $Q=P\,(d+1)^{2s^2}$: if $4Q\big(\log(2C)+\log(d+1)+2U\big)\le\log N$ and
--   $$e^{-U}\le\mathbb E_{n<M}\,\big(f(a_0+q_0n)-b\big)\,A(n),$$
--   then there are natural numbers $q,a,\mathrm{len}$ with $q>0$, $\mathrm{len}>1$, $a+qn<N$ for all $n<\mathrm{len}$, $e^{\log N/(4Q)}\le\mathrm{len}$, $\log\log N-\big(\log(4P)+2s^2\log(d+1)\big)\le\log\log\mathrm{len}$, and $b<\mathbb E_{n<\mathrm{len}}f(a+qn)$. Averages $\mathbb E_{n<M}$ are uniform over $\mathrm{Fin}\,M$; logarithms are natural.
--
--   Lean: `OAI.Erdos3.sliced_polynomial_patch_reset` in `lean/OAI/Combinatorics/Progressions/Polynomial/SlicedPolynomialPatchReset.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B094` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/SlicedPolynomialPatchReset.lean#L71

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B094

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sliced_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) 1 →
        let Q := P * (d + 1) ^ (2 * s * s)
        4 * (Q : ℝ) * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.exp (Real.log N / (4 * Q)) ≤ len ∧
          Real.log (Real.log N) -
            (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1)) ≤
              Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  sorry

end Erdos3
end
end OAI
