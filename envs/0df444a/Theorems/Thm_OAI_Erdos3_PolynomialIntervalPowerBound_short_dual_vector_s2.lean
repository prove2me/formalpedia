-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_short_dual_vector_s2
-- name    : OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:20:51.674156+00:00
-- url     : https://prove2.me/theorems/b6dfc424-94f6-438a-b131-7b46e6b21ce8
-- title:
--   A polynomial Weyl interval bound turns a small lattice Gaussian mean into a short dual vector with a rational approximation
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and let $k, C, d$ be natural numbers such that `PolynomialIntervalPowerBound k C d` holds. This is a proposition defined by OpenAI: for every real polynomial $P$ with $\deg P \le k$, all integers $u, v$ with $(v-u)_+ > 0$ (writing $M = (v-u)_+$, the truncation to $\mathbb{N}$), and every real $\delta$ with $0 < \delta \le 1$, $C \le \delta^d M$ and $\delta M \le \bigl|\sum_{n=u}^{v-1} e(P(n))\bigr|$ (with $e(x) = e^{2\pi i x}$), there exist a natural number $q$ with $0 < q \le C/\delta^d$ and an integer $p$ with $|q\,a_k - p| \le C/(\delta^d M^k)$, where $a_k$ is the coefficient of $X^k$ in $P$.
--
--   Let $\Lambda \subseteq E$ be a full-rank discrete $\mathbb{Z}$-lattice (a $\mathbb{Z}$-submodule with the discrete topology satisfying `IsZLattice ℝ Λ`), let $t > 0$ be real, $\alpha \in E$, and $N$ a natural number. Write $A = $ `normalizedLatticeGaussian Λ t 0`, where `normalizedLatticeGaussian Λ t x` $= (\sqrt t)^{\dim E}\operatorname{covol}(\Lambda)\sum_{m \in \Lambda} e^{-\pi t \|x - m\|^2}$ (defined by OpenAI). Assume
--   - $C\,(8A)^d \le 2N + 1$, and
--   - `latticeGaussianMean Λ t k α N` $< 1/2$, where `latticeGaussianMean Λ t k α N` (defined by OpenAI) is the average of `normalizedLatticeGaussian Λ t` $(n^k \alpha)$ over the integers $n \in [-N, N]$.
--
--   Then there is a vector $\xi \in E$ such that $\xi$ lies in the Euclidean dual lattice `euclideanDualLattice Λ` (the set of $\xi$ with $\langle \xi, x\rangle \in \mathbb{Z}$ for all $x \in \Lambda$), $\xi \ne 0$, and $\|\xi\| \le \sqrt t \cdot$ `schmidtRadiusFactor (dim E) A`, where `schmidtRadiusFactor D A` $= 4(D + \log A + 1)$ (defined by OpenAI) and $\dim E$ is the real dimension of $E$; and there are a natural number $q$ with $0 < q \le C\,(8A)^d$ and an integer $p$ with
--   $$\bigl|q\,\langle \xi, \alpha\rangle - p\bigr| \le \frac{C\,(8A)^d}{(2N+1)^k}.$$
--
--   Lean: `OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector_s2`, which states OpenAI's `OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector` (in `lean/OAI/Combinatorics/Progressions/Polynomial/SchmidtShortDualVector.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B100`, `OAIE3v2B137` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/SchmidtShortDualVector.lean (declaration OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B137

section

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.short_dual_vector_s2 {k C d : ℕ}
    (hW : PolynomialIntervalPowerBound k C d)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ)
    (hsize : (C : ℝ) * (8 * normalizedLatticeGaussian Λ t 0) ^ d ≤ 2 * N + 1)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧
      ‖ξ‖ ≤ Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ∧
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (8 * normalizedLatticeGaussian Λ t 0) ^ d ∧
        ∃ p : ℤ, |(q : ℝ) * inner ℝ ξ α - p| ≤
          C * (8 * normalizedLatticeGaussian Λ t 0) ^ d / (2 * (N : ℝ) + 1) ^ k := by
  sorry

end Erdos3

end

end OAI
end
