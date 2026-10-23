-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_5_5
-- name    : IntuitiveDPI.Smooth.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:32.062985+00:00
-- url     : https://prove2.me/theorems/a12845fe-8435-45f5-9610-d3e678cafb73
-- title:
--   Lemma 5.5, p. 7 — non-conditional QAEP for H_0: H(A)_ρ ≥ lim_{ε→0} lim_{n→∞} (1/n) H_0^ε(A^n)_{ρ^{⊗n}}
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_A$. Then
--   $$H(A)_\rho\ge\lim_{\varepsilon\to0}\lim_{n\to\infty}\frac1n H^\varepsilon_0(A^n)_{\rho^{\otimes n}},$$
--   where $H^\varepsilon_0(A^n)_{\rho^{\otimes n}}=\min_{\rho'\in\mathcal B^\varepsilon(\rho^{\otimes n})}\log\operatorname{rank}\rho'$ is the smooth 0th order Rényi entropy of the tensor power.
--
--   This is the other half of the non-conditional QAEP: a nearby state of $\rho^{\otimes n}$ has rank at most about $2^{nH(A)_\rho}$, which is Schumacher's compression bound. It is used, through the chain rule, in Lemma 4.1.
--
--   **Formalization Note** The double limit $\lim_{\varepsilon\to0}\lim_{n\to\infty}$ is written with the predicates of the definitions module: `IidLowerLimit L f` means that for every $\delta>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, eventually in $n$, $L-\delta\le f(\varepsilon,n)$ (that is, $L\le\lim_{\varepsilon\to0^+}\liminf_n f$); `IidUpperLimit L f` is the mirror image $f(\varepsilon,n)\le L+\delta$. The paper does not prove that the inner limit in $n$ exists, and its proofs bound only the inner quantity, so no existence of the inner limit is asserted. Here $L=H(A)_\rho$ and $f(\varepsilon,n)=\frac1n H^\varepsilon_0(A^n)_{\rho^{\otimes n}}$ in `EReal`. The paper's proof cites its Lemma 5.3, (30), which is false as printed (at $\varepsilon=0$ it reads $H_0\le H_\alpha$ for $\alpha<1$); Lemma 5.5 itself is true and is stated here on its own, without (30).
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 7, Lemma 5.5, (34)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma 5.5, (34), p. 7: `H(A)_ρ ≥ lim_{ε→0} lim_{n→∞} (1/n) H^ε_0(A^n)_{ρ^{⊗n}}`,
in the reading `IidUpperLimit`. -/
theorem lemma_5_5 {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    IidUpperLimit (vnEntropy ρ)
      (fun ε n => (((n : ℝ)⁻¹ : ℝ) : EReal) * smoothZeroEntropy (piKron n ρ) ε) := by sorry

end IntuitiveDPI.Smooth
