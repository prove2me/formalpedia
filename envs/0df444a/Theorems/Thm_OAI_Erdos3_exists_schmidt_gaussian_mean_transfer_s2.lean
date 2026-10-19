-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_schmidt_gaussian_mean_transfer_s2
-- name    : OAI.Erdos3.exists_schmidt_gaussian_mean_transfer_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:20.64381+00:00
-- url     : https://prove2.me/theorems/9e9cb805-d878-4fa1-a99f-db17c3824197
-- title:
--   Transferring a lattice Gaussian mean to the hyperplane sublattice orthogonal to a short dual vector
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and $\Lambda \subseteq E$ a full-rank discrete $\mathbb{Z}$-lattice (a $\mathbb{Z}$-submodule with the discrete topology satisfying `IsZLattice ℝ Λ`). Let $\xi \in E$ with $\xi \ne 0$ and $\xi$ in the Euclidean dual lattice `euclideanDualLattice Λ` (the set of $\xi$ with $\langle \xi, x\rangle \in \mathbb{Z}$ for all $x \in \Lambda$). Let $w \in \Lambda$ with $\langle \xi, w\rangle = 1$, and let $\alpha \in E$, $N, k$ natural numbers and $t, \varepsilon$ real numbers with $t > 0$ and $0 \le \varepsilon \le 1$. Let $H = \ker\langle \xi, \cdot\rangle$ (the kernel of `normalFunctional ξ`, the real linear functional $x \mapsto \langle \xi, x\rangle$), and let $\Lambda_H$ = `latticeHyperplane Λ (normalFunctional ξ)`, the lattice $\Lambda \cap H$ viewed inside $H$. Assume $\dim_{\mathbb{R}} H \cdot \varepsilon \le 1$ and
--   $$\sqrt t \cdot N^k \cdot \frac{\|\langle \xi, \alpha\rangle\|_{\mathbb{R}/\mathbb{Z}}}{\|\xi\|} \le \varepsilon,$$
--   where $\|\theta\|_{\mathbb{R}/\mathbb{Z}}$ (`integerDistance`) is the distance from $\theta$ to the nearest integer.
--
--   Then there is $\beta \in H$ such that
--   $$e^{-4\pi}\sqrt t\cdot \texttt{latticeGaussianMean}\ \Lambda_H\ \bigl(t(1+\varepsilon)^2\bigr)\ k\ \beta\ N \le e\,\|\xi\|\cdot \texttt{latticeGaussianMean}\ \Lambda\ t\ k\ \alpha\ N$$
--   and
--   $$\sqrt t\cdot \texttt{normalizedLatticeGaussian}\ \Lambda_H\ \bigl(t(1+\varepsilon)^2\bigr)\ 0 \le e\,\|\xi\|\cdot \texttt{normalizedLatticeGaussian}\ \Lambda\ t\ 0.$$
--   Here, for a lattice $\Gamma$ in a Euclidean space $F$, `normalizedLatticeGaussian Γ t x` $= (\sqrt t)^{\dim F}\operatorname{covol}(\Gamma)\sum_{m \in \Gamma} e^{-\pi t\|x - m\|^2}$ and `latticeGaussianMean Γ t k α N` is the average of `normalizedLatticeGaussian Γ t` $(n^k\alpha)$ over the integers $n \in [-N, N]$ (both defined by OpenAI).
--
--   Lean: `OAI.Erdos3.exists_schmidt_gaussian_mean_transfer_s2`, which states OpenAI's `OAI.Erdos3.exists_schmidt_gaussian_mean_transfer` (in `lean/OAI/Combinatorics/Progressions/Polynomial/SchmidtGaussianMean.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B067` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/SchmidtGaussianMean.lean (declaration OAI.Erdos3.exists_schmidt_gaussian_mean_transfer)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B067

section

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_schmidt_gaussian_mean_transfer_s2 (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0) (hξdual : ξ ∈ euclideanDualLattice Λ)
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hbudget : (Module.finrank ℝ (normalFunctional ξ).ker : ℝ) * ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker,
      Real.exp (-4 * Real.pi) * Real.sqrt t *
          latticeGaussianMean (latticeHyperplane Λ (normalFunctional ξ))
            (t * (1 + ε) ^ 2) k β N ≤
        Real.exp 1 * ‖ξ‖ * latticeGaussianMean Λ t k α N ∧
      Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) 0 ≤
        Real.exp 1 * ‖ξ‖ * normalizedLatticeGaussian Λ t 0 := by
  sorry

end Erdos3

end

end OAI
end
