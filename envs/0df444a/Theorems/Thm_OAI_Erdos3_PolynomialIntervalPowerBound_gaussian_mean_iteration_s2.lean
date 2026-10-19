-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_gaussian_mean_iteration_s2
-- name    : OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:20:24.285121+00:00
-- url     : https://prove2.me/theorems/605c2bbe-292c-4969-94d6-2720089c1be3
-- title:
--   A Weyl-type inverse bound at degree j+1 gives a lower bound on the lattice Gaussian mean along n^(j+1) α
-- statement:
--   Let $j, C, e, D$ be natural numbers and suppose `PolynomialIntervalPowerBound (j+1) C e` holds. This is a proposition defined by OpenAI (an inverse theorem for Weyl sums): for every real polynomial $P$ with $\deg P \le j+1$, all integers $u, v$ with $L := \max(v-u, 0) > 0$, and every $\delta$ with $0 < \delta \le 1$, $C \le \delta^e L$ and $\delta L \le \bigl|\sum_{n=u}^{v-1} \exp(2\pi i P(n))\bigr|$, there are a natural number $q$ with $0 < q \le C/\delta^e$ and an integer $p$ with $|q \cdot \operatorname{coeff}_{j+1}(P) - p| \le C / (\delta^e L^{j+1})$.
--
--   Let $M, U, V$ be real numbers with $1 \le M$, $1 \le U$, $\exp(1) \cdot \texttt{schmidtRadiusFactor}\ D\ U \le M$, $2 \le V$, $4\,\texttt{schmidtStepFactor}\ C\ e\ D\ U + 1 \le V$, and
--   $$2\, \exp(4\pi + 1)\, \texttt{schmidtRadiusFactor}\ D\ U \cdot \texttt{schmidtStepFactor}\ C\ e\ D\ U \le V.$$
--   Here (definitions by OpenAI) `schmidtRadiusFactor d A` $= 4(d + \log A + 1)$ and `schmidtStepFactor C e d A` $= 1 + C\,(8A)^e\,(\exp(\pi)\, A)\,(\texttt{schmidtRadiusFactor}\ d\ A + d + 1)$.
--
--   Let $d$ be a natural number. Then for every finite-dimensional real inner product space $E$ (with its Borel σ-algebra), every lattice $\Lambda \subseteq E$ (a discrete $\mathbb{Z}$-submodule spanning $E$, i.e. a full-rank $\mathbb{Z}$-lattice), every real $t > 0$, every $\alpha \in E$ and every natural number $N$: if $\dim_{\mathbb{R}} E = d$, $d \le D$, and $\texttt{normalizedLatticeGaussian}\ \Lambda\ t\ 0 \cdot M^d \le U$, then
--   $$1 \le V^{d+1} \cdot \texttt{latticeGaussianMean}\ \Lambda\ t\ (j+1)\ \alpha\ N.$$
--   Here (definitions by OpenAI) `normalizedLatticeGaussian Λ t x` $= (\sqrt t)^{\dim E}\, \operatorname{covol}(\Lambda) \sum_{m \in \Lambda} \exp(-\pi t \|x - m\|^2)$, and `latticeGaussianMean Λ t k α N` is the average of `normalizedLatticeGaussian Λ t` $(n^k \alpha)$ over the integers $n$ with $-N \le n \le N$.
--
--   Lean: `OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration_s2`, which states OpenAI's `OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B100`, `OAIE3v2B137` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean (declaration OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B137

section

namespace OAI

section

namespace Erdos3

theorem PolynomialIntervalPowerBound.gaussian_mean_iteration_s2
    {j C e D : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {M U V : ℝ} (hM : 1 ≤ M) (hU : 1 ≤ U)
    (hLM : Real.exp 1 * schmidtRadiusFactor D U ≤ M)
    (hV : 2 ≤ V) (hKV : 4 * schmidtStepFactor C e D U + 1 ≤ V)
    (hTV : 2 * Real.exp (4 * Real.pi + 1) * schmidtRadiusFactor D U *
      schmidtStepFactor C e D U ≤ V) (d : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
      {t : ℝ}, 0 < t → ∀ (α : E) (N : ℕ),
      Module.finrank ℝ E = d → d ≤ D →
      normalizedLatticeGaussian Λ t 0 * M ^ d ≤ U →
      1 ≤ V ^ (d + 1) * latticeGaussianMean Λ t (j + 1) α N := by
  sorry

end Erdos3

end

end OAI
end
