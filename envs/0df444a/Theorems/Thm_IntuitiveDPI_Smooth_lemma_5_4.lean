-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_5_4
-- name    : IntuitiveDPI.Smooth.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:22.959988+00:00
-- url     : https://prove2.me/theorems/aef86094-723b-42ae-8bef-f04da6a8d766
-- title:
--   Lemma 5.4, p. 6 — non-conditional QAEP for the smooth min-entropy: H(A)_ρ ≤ lim_{ε→0} lim_{n→∞} (1/n) H_min^ε(A^n)_{ρ^{⊗n}}
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_A$. Then
--   $$H(A)_\rho\le\lim_{\varepsilon\to0}\lim_{n\to\infty}\frac1n H^\varepsilon_{\min}(A^n)_{\rho^{\otimes n}},$$
--   where $H^\varepsilon_{\min}(A^n)_{\rho^{\otimes n}}$ is the non-conditional smooth min-entropy of the $n$-fold tensor power.
--
--   This is one half of the non-conditional QAEP (Schumacher compression). Together with the chain rule it gives the lower bound of the conditional QAEP, Lemma 4.1.
--
--   **Formalization Note** The double limit $\lim_{\varepsilon\to0}\lim_{n\to\infty}$ is written with the predicates of the definitions module: `IidLowerLimit L f` means that for every $\delta>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, eventually in $n$, $L-\delta\le f(\varepsilon,n)$ (that is, $L\le\lim_{\varepsilon\to0^+}\liminf_n f$); `IidUpperLimit L f` is the mirror image $f(\varepsilon,n)\le L+\delta$. The paper does not prove that the inner limit in $n$ exists, and its proofs bound only the inner quantity, so no existence of the inner limit is asserted. Here $L=H(A)_\rho$ (`vnEntropy`, bits), $f(\varepsilon,n)=\frac1n H^\varepsilon_{\min}(A^n)_{\rho^{\otimes n}}$ in `EReal`, and $\rho^{\otimes n}$ is `QAlgorithms.piKron n ρ` on `Fin n → A`.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 6, Lemma 5.4, (31)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma 5.4, (31), p. 6: `H(A)_ρ ≤ lim_{ε→0} lim_{n→∞} (1/n) H^ε_min(A^n)_{ρ^{⊗n}}`,
in the reading `IidLowerLimit`. -/
theorem lemma_5_4 {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    IidLowerLimit (vnEntropy ρ)
      (fun ε n => (((n : ℝ)⁻¹ : ℝ) : EReal) * smoothMinEntropy (piKron n ρ) ε) := by sorry

end IntuitiveDPI.Smooth
