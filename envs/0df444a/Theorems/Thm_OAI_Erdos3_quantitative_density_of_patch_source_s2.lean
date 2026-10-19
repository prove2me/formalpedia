-- Prove2me | Theorems.Thm_OAI_Erdos3_quantitative_density_of_patch_source_s2
-- name    : OAI.Erdos3.quantitative_density_of_patch_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:41:50.880775+00:00
-- url     : https://prove2.me/theorems/49b0a8b7-ef31-4381-8d2f-1260540964dd
-- title:
--   A subquadratic patch source for k-AP-free intervals implies the quantitative density bound for k-term progressions
-- statement:
--   Let $k, s$ be natural numbers with $k > 0$, and let $\kappa, H_0, K, q, A_0, B, D, p_{\min}, C_{\mathrm{src}}$ be real numbers with $\kappa > 0$, $\kappa H_0 > 1$, $K \ge 2$, $1 \le q < 2$, $A_0 > 0$, $B > 0$ and $D > 0$. Assume `SubquadraticPatchSource k s κ H₀ K q A₀ B D pmin Csrc`, a proposition defined by OpenAI: with $\mu = \frac{\log q}{4 \log K}$ and $\beta = 1 - (\frac{\log 2}{4 \log K} - \mu)/2$, for every $k$-AP-free interval $S$ (OpenAI's `APFreeInterval k`: a length $\ell > 1$ and a nonempty set of points in $\{0, \dots, \ell - 1\}$ containing no $k$-term arithmetic progression $a, a+d, \dots, a+(k-1)d$ with $d > 0$) whose parameter $\pi = \max(2, \log(2/\alpha))$, where $\alpha$ is the density (number of points)$/\ell$, satisfies $p_{\min} \le \pi$ and $A_0 \pi^\beta + C_{\mathrm{src}} \le \log\log \ell$, there are natural numbers $d, M, a, q_0$, a real $U$ and a `PolynomialPatch Unit s d` $P$ with $q_0 > 0$, $a + q_0 n < \ell$ for all $n < M$, $U \ge 1$, $\log \ell - U \le \log M$, $\mathrm{lip}(P) + 1 \le e^U$ (lip the Lipschitz constant of the patch kernel), $\log(d+1) \le B \pi^\mu \log(2 + \pi)$, $\log U \le D \pi^{1/4} \log(2 + \pi)$, and
--   $$e^{-U} \le \mathbb{E}_{n \in \operatorname{Fin} M} \bigl( \mathbf{1}_S(a + q_0 n) - G \alpha \bigr) \cdot P.\mathrm{value}(n),$$
--   where $G = \kappa \cdot g_{\lfloor \mu' \log \pi \rfloor} / 2$, $\mu' = 1/(4 \log K)$, and $g$ is OpenAI's `amplificationGain κ H₀` ($g_0 = H_0$, $g_{t+1} = \kappa g_t^2$).
--
--   Then `QuantitativeDensityBound k` holds: there are reals $C, c, \eta > 0$ such that for every natural number $N \ge 3$, the largest size of a subset of $\{1, \dots, N\}$ containing no $k$-term arithmetic progression (with positive common difference) is at most $C N \exp\bigl(-c (\log\log N)^{1+\eta}\bigr)$.
--
--   Lean: `OAI.Erdos3.quantitative_density_of_patch_source_s2`, which states OpenAI's `OAI.Erdos3.quantitative_density_of_patch_source` (in `lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean (declaration OAI.Erdos3.quantitative_density_of_patch_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem quantitative_density_of_patch_source_s2 {k s : ℕ} (hk : 0 < k)
    {κ H₀ K q A₀ B D pmin Csrc : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2)
    (hA : 0 < A₀) (hB : 0 < B) (hD : 0 < D)
    (hsource : SubquadraticPatchSource k s κ H₀ K q A₀ B D pmin Csrc) :
    QuantitativeDensityBound k := by
  sorry

end Erdos3

end

end OAI
end
