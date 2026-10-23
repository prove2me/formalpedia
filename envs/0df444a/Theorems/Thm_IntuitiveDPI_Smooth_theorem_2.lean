-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_theorem_2
-- name    : IntuitiveDPI.Smooth.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:38.962108+00:00
-- url     : https://prove2.me/theorems/9f004e17-a6f1-4a18-b61d-3e2f0041b82c
-- title:
--   Theorem 2, p. 3 — QAEP: lim_{ε→0} lim_{n→∞} (1/n) H_min^ε(A^n|B^n)_{ρ^{⊗n}} = H(A|B)_ρ
-- statement:
--   Let $\rho=\rho_{AB}$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$. Then the regularized smooth conditional min-entropy of its i.i.d. copies is the conditional von Neumann entropy:
--   $$\lim_{\varepsilon\to0}\lim_{n\to\infty}\frac1n H^\varepsilon_{\min}(A^n|B^n)_{\rho^{\otimes n}}=H(A|B)_\rho.$$
--
--   This is the quantum asymptotic equipartition property. Applied to $\rho_{A(BC)}$ and to $\rho_{AB}$ it reduces the von Neumann entropy data processing inequality $H(A|BC)_\rho\le H(A|B)_\rho$ (Theorem 3) to the smooth min-entropy one (Theorem 1).
--
--   **Formalization Note** The double limit $\lim_{\varepsilon\to0}\lim_{n\to\infty}$ is written with the predicates of the definitions module: `IidLowerLimit L f` means that for every $\delta>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, eventually in $n$, $L-\delta\le f(\varepsilon,n)$ (that is, $L\le\lim_{\varepsilon\to0^+}\liminf_n f$); `IidUpperLimit L f` is the mirror image $f(\varepsilon,n)\le L+\delta$. The paper does not prove that the inner limit in $n$ exists, and its proofs bound only the inner quantity, so no existence of the inner limit is asserted. The equality is the conjunction `IidLowerLimit ∧ IidUpperLimit` with $L=H(A|B)_\rho$ (`conditionalEntropy`) and $f(\varepsilon,n)=\frac1n H^\varepsilon_{\min}(A^n|B^n)_{\rho^{\otimes n}}$, $\rho^{\otimes n}$ = `groupedPower ρ n`; it is the conjunction of Lemmas 4.1 and 4.2.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 3, Theorem 2, (5)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Theorem 2, (5), p. 3 (QAEP):
`lim_{ε→0} lim_{n→∞} (1/n) H^ε_min(A^n|B^n)_{ρ^{⊗n}} = H(A|B)_ρ`, in the reading
`IidLowerLimit ∧ IidUpperLimit`. -/
theorem theorem_2 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    IidLowerLimit (conditionalEntropy ρ)
        (fun ε n => (((n : ℝ)⁻¹ : ℝ) : EReal) *
          smoothConditionalMinEntropy (groupedPower ρ n) ε) ∧
      IidUpperLimit (conditionalEntropy ρ)
        (fun ε n => (((n : ℝ)⁻¹ : ℝ) : EReal) *
          smoothConditionalMinEntropy (groupedPower ρ n) ε) := by sorry

end IntuitiveDPI.Smooth
