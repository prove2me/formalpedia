-- Prove2me | Theorems.Thm_OAI_Erdos3_subquadratic_patch_source_of_relative_family_s2
-- name    : OAI.Erdos3.subquadratic_patch_source_of_relative_family_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:55:36.373704+00:00
-- url     : https://prove2.me/theorems/9c7081fe-f639-4921-9150-96a58ed1f2b7
-- title:
--   A relative patch power rule and low-density absolute rules give a subquadratic source
-- statement:
--   Let $s, n_0, C, E$ be natural numbers and $\tau, H_0$ reals, and put $\kappa = (1 - \tau)^{s+1}$. Assume $C \ge 1$, $E \ge 2$, `RelativePatchPowerInductionRule s n₀ s τ E` (OpenAI's `RelativePatchInductionRule s n₀ s τ cutoff cost` with $\mathrm{cutoff}(p) = \mathrm{cost}(p) = (p+2)^E$: a proposition asserting that, under stated size, density, progression-freeness and patch-score hypotheses, `RelativePatchSliceConclusion` holds), $0 < \kappa < 1$, $H_0 > 1$, $1 \le \kappa^2 H_0$, and that for every real $p$ with $p \ge 2$ and $n_0 \le p$ and every natural number $j$,
--   `LowDensityRelativeAbsoluteRule s n₀ p (amplificationGain κ H₀ j) ((s+1)^j * ⌊(p+2)^C⌋) (amplificationResource p (C+1) (E+1) j)` holds. Here `LowDensityRelativeAbsoluteRule s n₀ p H D x` says that for every real $a$ with $e^{-p} \le a$, $a > 0$ and $H^2 a \le 1$, `RelativePatchAbsoluteRule s n₀ x a (H a) D` holds (a proposition of OpenAI asserting `RelativePatchSliceConclusion` for functions on boxes of distinct, comparable primes of size at least $e^x$ with mean at least $a$ and progression-free support); `amplificationGain κ H₀` is the sequence $g_0 = H_0$, $g_{j+1} = \kappa g_j^2$; and `amplificationResource p D K` is the sequence $r_0 = (2+p)^D$, $r_{j+1} = (2 + r_j)^K$.
--
--   Then there is a real $p_{\min}$ with
--   `SubquadraticPatchSource (s + 2) s κ H₀ (E + 1) 1 1 B' D' pmin (log 2)`, where $B' =$ `amplificationSourceRankLogConstant (s+1) C (E+1)` $= 1 + \mathrm{levelCoefficient}(E+1) \log(s+1) + C$ and $D' =$ `amplificationSourceLogCoefficient (C+1) E` $= E\,(C + 4)$. Here `levelCoefficient K` $= 1/(4 \log K)$, and `SubquadraticPatchSource k s κ H₀ K q A₀ B D pmin Csrc` is the proposition: with $\mu = \mathrm{levelCoefficient}(K)\log q$ and $\beta = 1 - (\mathrm{levelCoefficient}(K)\log 2 - \mu)/2$, for every `APFreeInterval k` $S$ (a length $\ell > 1$ and a nonempty set $A_S \subseteq \{0, \dots, \ell-1\}$ with no $k$-term arithmetic progression, of density $\alpha = |A_S|/\ell$ and parameter $\pi = \max(2, \log(2/\alpha))$) with $p_{\min} \le \pi$ and $A_0 \pi^\beta + C_{\mathrm{src}} \le \log\log \ell$, there exist natural numbers $d, M, a, q_0$, a real $U$ and a `PolynomialPatch Unit s d` $A$ with $q_0 > 0$, $a + q_0 n < \ell$ for all $n < M$, $U \ge 1$, $\log \ell - U \le \log M$, $A.\mathrm{kernel.lip} + 1 \le e^U$, $\log(d+1) \le B \pi^\mu \log(2+\pi)$, $\log U \le D \pi^{1/4} \log(2+\pi)$, and $e^{-U} \le \mathbb E_{n \in \mathrm{Fin}\,M} (\mathbf 1_{A_S}(a + q_0 n) - G\alpha)\, A.\mathrm{value}(n)$ with $G = \kappa\, g_{\lfloor \mathrm{levelCoefficient}(K) \log \pi \rfloor}/2$.
--
--   Lean: `OAI.Erdos3.subquadratic_patch_source_of_relative_family_s2`, which states OpenAI's `OAI.Erdos3.subquadratic_patch_source_of_relative_family` (in `lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean (declaration OAI.Erdos3.subquadratic_patch_source_of_relative_family)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252

section

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

theorem subquadratic_patch_source_of_relative_family_s2
    {s n₀ C E : ℕ} {τ H₀ : ℝ}
    (hC : 1 ≤ C) (hE : 2 ≤ E)
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hκ : 0 < (1 - τ) ^ (s + 1)) (hκ1 : (1 - τ) ^ (s + 1) < 1)
    (hH : 1 < H₀) (hκH : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H₀)
    (hfamily : ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
      LowDensityRelativeAbsoluteRule s n₀ p
        (amplificationGain ((1 - τ) ^ (s + 1)) H₀ j)
        ((s + 1) ^ j * ⌊(p + 2) ^ C⌋₊)
        (amplificationResource p (C + 1) (E + 1) j)) :
    ∃ pmin : ℝ, SubquadraticPatchSource (s + 2) s
      ((1 - τ) ^ (s + 1)) H₀ (E + 1) 1 1
      (amplificationSourceRankLogConstant (s + 1) C (E + 1))
      (amplificationSourceLogCoefficient (C + 1) E) pmin (Real.log 2) := by
  sorry

end Erdos3

end

end OAI
end
