-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_4_1
-- name    : IntuitiveDPI.Smooth.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:32.138389+00:00
-- url     : https://prove2.me/theorems/5ae4833c-6dbe-4789-9637-bc5ddca10251
-- title:
--   Lemma 4.1, p. 4 — lower bound: H(A|B)_ρ ≤ lim_{ε→0} lim_{n→∞} (1/n) H_min^ε(A^n|B^n)_{ρ^{⊗n}}
-- statement:
--   Let $\rho=\rho_{AB}$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$, with conditional von Neumann entropy $H(A|B)_\rho=H(AB)_\rho-H(B)_\rho$. Then
--   $$H(A|B)_\rho\le\lim_{\varepsilon\to0}\lim_{n\to\infty}\frac1n H^\varepsilon_{\min}(A^n|B^n)_{\rho^{\otimes n}},$$
--   where $\rho^{\otimes n}$ is regarded as a state on $A^n\otimes B^n$.
--
--   This is the lower half of the quantum asymptotic equipartition property (Theorem 2).
--
--   **Formalization Note** The double limit $\lim_{\varepsilon\to0}\lim_{n\to\infty}$ is written with the predicates of the definitions module: `IidLowerLimit L f` means that for every $\delta>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, eventually in $n$, $L-\delta\le f(\varepsilon,n)$ (that is, $L\le\lim_{\varepsilon\to0^+}\liminf_n f$); `IidUpperLimit L f` is the mirror image $f(\varepsilon,n)\le L+\delta$. The paper does not prove that the inner limit in $n$ exists, and its proofs bound only the inner quantity, so no existence of the inner limit is asserted. Here $L=H(A|B)_\rho$ (`conditionalEntropy` of `Information100.P67`) and $f(\varepsilon,n)=\frac1n H^\varepsilon_{\min}(A^n|B^n)_{\rho^{\otimes n}}$, with $\rho^{\otimes n}$ = `groupedPower ρ n` on `(Fin n → A) × (Fin n → B)`, so that the conditioning system is $B^n$.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 4, Lemma 4.1, (7)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma 4.1, (7), p. 4: `H(A|B)_ρ ≤ lim_{ε→0} lim_{n→∞} (1/n) H^ε_min(A^n|B^n)_{ρ^{⊗n}}`,
in the reading `IidLowerLimit`. -/
theorem lemma_4_1 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    IidLowerLimit (conditionalEntropy ρ)
      (fun ε n => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothConditionalMinEntropy (groupedPower ρ n) ε) := by sorry

end IntuitiveDPI.Smooth
