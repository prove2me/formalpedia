-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_lattice_recurrence
-- name    : OAI.Erdos3.PolynomialIntervalPowerBound.lattice_recurrence
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T04:21:31.801032+00:00
-- url     : https://prove2.me/theorems/59c816fb-55f9-42df-a0d0-bcf6a3038898
-- title:
--   The interval power bound gives a small q with q^(j+1) alpha near a lattice point
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with a measurable structure that is its Borel $\sigma$-algebra (section variables), and let $j, C, e$ be natural numbers with `PolynomialIntervalPowerBound (j+1) C e`. That is OpenAI's predicate `PolynomialIntervalPowerBound k C d`: for every real polynomial $P$ of degree at most $k$, all integers $u < v$ and every $0 < \delta \le 1$ with $C \le \delta^d (v-u)$ and $\delta(v-u) \le \bigl|\sum_{n=u}^{v-1} e(P(n))\bigr|$, there are $q \in \mathbb{N}$ with $0 < q \le C/\delta^d$ and $p \in \mathbb{Z}$ with $|q\,P_k - p| \le C/(\delta^d (v-u)^k)$, where $P_k$ is the coefficient of $x^k$ and $e(x) = e^{2\pi i x}$. Let $\Lambda \subseteq E$ be a full-rank discrete $\mathbb{Z}$-lattice, $\alpha \in E$, $N \in \mathbb{N}$, and $t, R$ real with $t > 0$ and $R \ge 0$. Put $n = \dim_{\mathbb{R}} E$ and $\Gamma = $ `normalizedLatticeGaussian Λ t 0` $= t^{n/2}\,\mathrm{covol}(\Lambda)\sum_{m \in \Lambda} e^{-\pi t \|m\|^2}$, and $Q = $ `schmidtMeanDenominator C e n Γ` (an explicit real-valued function of OpenAI). Assume $2Q\Gamma < 2N + 1$ and $2Q\,e^{-\pi t R^2/2}\,2^{n}\,\Gamma < 1$. Then there exist $q \in \mathbb{N}$ with $0 < q \le N$ and $v \in \Lambda$ with $\|q^{j+1}\alpha - v\| < R$.
--
--   Lean: `OAI.Erdos3.PolynomialIntervalPowerBound.lattice_recurrence` in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B039` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean#L614

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B039

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.lattice_recurrence {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α : E) (N : ℕ) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (hlength : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (htail : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      (Real.exp (-Real.pi * t * R ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
        normalizedLatticeGaussian Λ t 0) < 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ (j + 1) • α - v‖ < R := by
  sorry

end Erdos3
end
end OAI
