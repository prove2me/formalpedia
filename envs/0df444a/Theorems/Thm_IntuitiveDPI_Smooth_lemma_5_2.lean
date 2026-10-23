-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_5_2
-- name    : IntuitiveDPI.Smooth.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:39.281044+00:00
-- url     : https://prove2.me/theorems/0c848aae-b3c1-46b7-aff1-d370d16b3f0c
-- title:
--   Lemma 5.2, p. 6 — H_α(A)_ρ + log(1 − √(1 − ε²))/(α − 1) ≤ H_min^ε(A)_ρ for α > 1, ε ∈ (0, 1]
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_A$, let $\alpha>1$ and $\varepsilon\in(0,1]$. Then
--   $$H_\alpha(A)_\rho+\frac{\log\bigl(1-\sqrt{1-\varepsilon^2}\bigr)}{\alpha-1}\le H^\varepsilon_{\min}(A)_\rho,$$
--   where $H_\alpha(A)_\rho=\frac{1}{1-\alpha}\log\operatorname{Tr}\rho^\alpha$ is the Rényi entropy of order $\alpha$ and $H^\varepsilon_{\min}(A)_\rho$ the non-conditional smooth min-entropy.
--
--   The lower bound turns the Rényi entropy, which is additive on tensor powers, into a lower bound on the smooth min-entropy; it is the main step of the non-conditional QAEP for the smooth min-entropy (Lemma 5.4).
--
--   **Formalization Note** $H_\alpha$ is `renyiEntropy` of `Dependency50.P35`, which equals $\frac{1}{1-\alpha}\log_2\operatorname{Tr}\rho^\alpha$ for a density matrix and $\alpha\ne1$. Logarithms are base 2. For $\varepsilon\in(0,1]$ the argument $1-\sqrt{1-\varepsilon^2}$ of the logarithm is positive, so no junk value enters.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 6, Lemma 5.2, (26)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma 5.2, (26), p. 6: for a density matrix `ρ`, `α > 1` and `ε ∈ (0, 1]`,
`H_α(A)_ρ + log(1 - √(1 - ε²)) / (α - 1) ≤ H^ε_min(A)_ρ`. -/
theorem lemma_5_2 {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ)
    (α : ℝ) (hα : 1 < α) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((renyiEntropy α ρ + Real.logb 2 (1 - Real.sqrt (1 - ε ^ 2)) / (α - 1) : ℝ) : EReal) ≤
      smoothMinEntropy ρ ε := by sorry

end IntuitiveDPI.Smooth
