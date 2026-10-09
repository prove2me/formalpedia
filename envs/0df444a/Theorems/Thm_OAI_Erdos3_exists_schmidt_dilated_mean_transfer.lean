-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_schmidt_dilated_mean_transfer
-- name    : OAI.Erdos3.exists_schmidt_dilated_mean_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T06:39:43.409714+00:00
-- url     : https://prove2.me/theorems/b8dd73c4-6c2e-4e6c-8103-ad082f05996f
-- title:
--   Transfer of a polynomial Gaussian lattice mean to a dual hyperplane sublattice
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with a measurable structure that is its Borel $\sigma$-algebra (section variables), and $\Lambda \subseteq E$ a full-rank discrete $\mathbb{Z}$-lattice. For $x \in E$ and $t > 0$ write $\Gamma_\Lambda(t, x) = $ `normalizedLatticeGaussian Λ t x` $= t^{\dim E/2}\,\mathrm{covol}(\Lambda)\sum_{m \in \Lambda} e^{-\pi t\|x - m\|^2}$, and `latticeGaussianMean Λ t k α N` for the average of $\Gamma_\Lambda(t, n^k\alpha)$ over integers $n \in [-N, N]$. Let $\alpha, \xi, \zeta, w \in E$, $m, p \in \mathbb{Z}$ and $q, j, H, N \in \mathbb{N}$, with $m \ne 0$, $q > 0$, $\xi = m\zeta$, $\zeta \ne 0$, $\zeta$ in the dual lattice `euclideanDualLattice Λ` $= \{y : \langle y, \lambda\rangle \in \mathbb{Z} \ \forall \lambda \in \Lambda\}$, $w \in \Lambda$ with $\langle \zeta, w\rangle = 1$, and $N > 0$. Let $t, Q, B, S, \varepsilon, L, K$ be real numbers with $t > 0$, $Q, B, S, L \ge 0$, $0 \le \varepsilon \le 1$, and write $Z = \ker\langle\zeta, \cdot\rangle$ (the kernel of `normalFunctional ζ`) and $\Lambda_Z = $ `latticeHyperplane Λ (normalFunctional ζ)` (the lattice $\Lambda \cap Z$ in $Z$). Assume $(\dim Z)\,\varepsilon \le 1$, $\sqrt t \le \|\zeta\| S$, $\|\zeta\| \le \sqrt t\,L$, $|qm| \le Q$, $|q\langle\xi, \alpha\rangle - p| \le B/(2N+1)^{j+1}$, $HQ \le N$, $HBS \le \varepsilon N$, $1 \le K$ and $N \le 2KH$. Then there is $\beta \in Z$ with
--   $$\texttt{latticeGaussianMean}\ \Lambda_Z\ \bigl(t(1+\varepsilon)^2\bigr)\ (j+1)\ \beta\ H \le 2e^{4\pi + 1} L K\cdot \texttt{latticeGaussianMean}\ \Lambda\ t\ (j+1)\ \alpha\ N$$
--   and $\Gamma_{\Lambda_Z}(t(1+\varepsilon)^2, 0) \le e\,L\,\Gamma_\Lambda(t, 0)$.
--
--   Lean: `OAI.Erdos3.exists_schmidt_dilated_mean_transfer` in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B122` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean#L278

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B122

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

theorem exists_schmidt_dilated_mean_transfer
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α ξ ζ w : E) (m p : ℤ) (q j H N : ℕ)
    (hm : m ≠ 0) (hq : 0 < q) (hξ : ξ = (m : ℝ) • ζ)
    (hζ : ζ ≠ 0) (hζdual : ζ ∈ euclideanDualLattice Λ) (hwΛ : w ∈ Λ) (hw : inner ℝ ζ w = 1)
    (hN : 0 < N) {t Q B S ε L K : ℝ}
    (ht : 0 < t) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hbudget : (Module.finrank ℝ (normalFunctional ζ).ker : ℝ) * ε ≤ 1)
    (hs : Real.sqrt t ≤ ‖ζ‖ * S) (hnorm : ‖ζ‖ ≤ Real.sqrt t * L)
    (ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ Q)
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (2 * (N : ℝ) + 1) ^ (j + 1))
    (hHQ : (H : ℝ) * Q ≤ N) (hHBS : (H : ℝ) * B * S ≤ ε * N)
    (hK : 1 ≤ K) (hlength : (N : ℝ) ≤ 2 * K * H) :
    ∃ β : (normalFunctional ζ).ker,
      latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H ≤
        (2 * Real.exp (4 * Real.pi + 1) * L * K) * latticeGaussianMean Λ t (j + 1) α N ∧
      normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) 0 ≤ Real.exp 1 * L * normalizedLatticeGaussian Λ t 0 := by
  sorry

end Erdos3
end
end OAI
