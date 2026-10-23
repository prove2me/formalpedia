-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_B_2
-- name    : IntuitiveDPI.Smooth.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:25.829109+00:00
-- url     : https://prove2.me/theorems/55311c4c-c47a-41b6-b912-14c0b39c00c7
-- title:
--   Lemma B.2, p. 10 — lim_{α→1} H_α(A)_ρ = H(A)_ρ
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_A$. The Rényi entropies $H_\alpha(A)_\rho=\frac{1}{1-\alpha}\log\operatorname{Tr}\rho^\alpha$ converge to the von Neumann entropy $H(A)_\rho=-\operatorname{Tr}\rho\log\rho$ as $\alpha\to1$:
--   $$\lim_{\alpha\to1}H_\alpha(A)_\rho=H(A)_\rho.$$
--
--   The limit is taken from above in the proof of Lemma 5.4 and from below for Lemma 5.5.
--
--   **Formalization Note** The limit is two-sided and over $\alpha\ne1$ (the punctured neighbourhood `𝓝[≠] 1`), so the value of `renyiEntropy` (of `Dependency50.P35`) at $\alpha=1$ plays no role. $H(A)_\rho$ is `QAlgorithms.vnEntropy`, in bits.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 10, Lemma B.2, (B.5)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma B.2, (B.5), p. 10: `lim_{α→1} H_α(A)_ρ = H(A)_ρ` for a density matrix `ρ`. -/
theorem lemma_B_2 {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    Tendsto (fun α : ℝ => renyiEntropy α ρ) (𝓝[≠] 1) (𝓝 (vnEntropy ρ)) := by sorry

end IntuitiveDPI.Smooth
