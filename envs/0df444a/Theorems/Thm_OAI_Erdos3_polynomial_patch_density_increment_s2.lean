-- Prove2me | Theorems.Thm_OAI_Erdos3_polynomial_patch_density_increment_s2
-- name    : OAI.Erdos3.polynomial_patch_density_increment_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:21.484215+00:00
-- url     : https://prove2.me/theorems/2b7319e6-6f24-4246-87dc-1a7b95717ce1
-- title:
--   Correlation with a one-variable polynomial patch gives a density increment on a long arithmetic progression
-- statement:
--   Let $s$ be a natural number. Then there exist a real number $K \ge 1$ and a natural number $p > 0$ with the following property.
--
--   Let $d, N, T$ be natural numbers and $A$ a `PolynomialPatch Unit s d` (defined by OpenAI: $d$ weighted polynomial slots in one variable, of weights between $1$ and $s$, together with a patch kernel with Lipschitz constant `A.kernel.lip`; `A.value` is a real function of one real variable). Suppose
--   - $0 < T$, $K(d + 1) \le T$, $2^{s+1} s < T$, $24\, d\, s < T$, and $T^{(2p)^{s}\,(d+1)^{2s^2}} \le N$.
--
--   Let $f : \mathbb{N} \to \mathbb{R}$ with $f(n) \in [0, 1]$ for all $n < N$, and let $b, \sigma$ be real numbers with $b \in [0, 1]$, $\sigma > 0$,
--   - $8\cdot \texttt{A.kernel.lip}\cdot d\, s\, 2^{s} \le \sigma T$ and $2^{2s+3} \le \sigma T$, and
--   - $$\sigma \le \frac{1}{N}\sum_{n=0}^{N-1} \bigl(f(n) - b\bigr)\cdot \texttt{A.value}(n).$$
--
--   Then there exist natural numbers $q, a, \mathrm{len}$ with $0 < q$, $T \le \mathrm{len}$, $a + qn < N$ for all $n < \mathrm{len}$, and
--   $$b < \frac{1}{\mathrm{len}}\sum_{n=0}^{\mathrm{len}-1} f(a + qn).$$
--
--   Lean: `OAI.Erdos3.polynomial_patch_density_increment_s2`, which states OpenAI's `OAI.Erdos3.polynomial_patch_density_increment` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialPatchDensityIncrement.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B000`, `OAIE3v2B003` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialPatchDensityIncrement.lean (declaration OAI.Erdos3.polynomial_patch_density_increment)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B003

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_patch_density_increment_s2 (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (d N T : ℕ) (A : PolynomialPatch Unit s d), 0 < T →
        K * ((d : ℝ) + 1) ≤ T →
        (2 : ℝ) ^ (s + 1) * s < T → 24 * (d : ℝ) * s < T →
        T ^ ((2 * p) ^ s * (d + 1) ^ (2 * s * s)) ≤ N →
        ∀ f : ℕ → ℝ, (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        8 * (A.kernel.lip : ℝ) * d * s * (2 : ℝ) ^ s ≤ σ * T →
        (2 : ℝ) ^ (2 * s + 3) ≤ σ * T →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  sorry

end Erdos3

end

end OAI
end
