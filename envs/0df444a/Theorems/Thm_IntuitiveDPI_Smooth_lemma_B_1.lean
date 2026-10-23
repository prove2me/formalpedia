-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_B_1
-- name    : IntuitiveDPI.Smooth.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:34.028981+00:00
-- url     : https://prove2.me/theorems/a8cf8c61-df1b-4dc8-b339-adadabbe8870
-- title:
--   Lemma B.1, pp. 9–10 — almost-i.i.d. limit: lim_{ε→0} lim_{n→∞} (1/n) H(A^n|B^n)_{σ_n} = H(A|B)_ρ for σ_n ∈ B^ε(ρ^{⊗n})
-- statement:
--   Let $\rho=\rho_{AB}$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$, and for every $\varepsilon>0$ and $n$ let $\sigma_n=\sigma_{\varepsilon,n}\in\mathcal B^\varepsilon(\rho^{\otimes n})$ be a subnormalized state close to $\rho^{\otimes n}$ (on $A^n\otimes B^n$). Then
--   $$\lim_{\varepsilon\to0}\lim_{n\to\infty}\frac1nH(A^n|B^n)_{\sigma_n}=H(A|B)_\rho,$$
--   where $H(A^n|B^n)_{\sigma_n}$ is the conditional entropy (36) of the subnormalized state $\sigma_n$.
--
--   The conditional entropy rate is continuous at i.i.d. states in this sense; with Lemma 5.6 it gives the upper half of the QAEP (Lemma 4.2).
--
--   **Formalization Note** The double limit $\lim_{\varepsilon\to0}\lim_{n\to\infty}$ is written with the predicates of the definitions module: `IidLowerLimit L f` means that for every $\delta>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, eventually in $n$, $L-\delta\le f(\varepsilon,n)$ (that is, $L\le\lim_{\varepsilon\to0^+}\liminf_n f$); `IidUpperLimit L f` is the mirror image $f(\varepsilon,n)\le L+\delta$. The paper does not prove that the inner limit in $n$ exists, and its proofs bound only the inner quantity, so no existence of the inner limit is asserted. Here the equality is the conjunction `IidLowerLimit ∧ IidUpperLimit` with $L=H(A|B)_\rho$ and $f(\varepsilon,n)=\frac1n H(A^n|B^n)_{\sigma_{\varepsilon,n}}$, for every choice function $(\varepsilon,n)\mapsto\sigma_{\varepsilon,n}$ in the balls. Because $\sigma_n$ lies in the ball, it is subnormalized, and its conditional entropy is (36) (`condEntropySub`), as in the paper's use of the lemma on the $\tilde\rho$ of Lemma 5.6.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, pp. 9–10, Lemma B.1, (B.1)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma B.1, (B.1), pp. 9–10: for a density matrix `ρ` on `A ⊗ B` and any choice of
subnormalized `σ_n ∈ B^ε(ρ^{⊗n})` (for every `ε > 0` and `n`),
`lim_{ε→0} lim_{n→∞} (1/n) H(A^n|B^n)_{σ_n} = H(A|B)_ρ`, with `H(·|·)` of (36), in the reading
`IidLowerLimit ∧ IidUpperLimit`. -/
theorem lemma_B_1 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ)
    (σ : ℝ → (n : ℕ) → Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ)
    (hσ : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      IsSubnormalized (σ ε n) ∧ purifiedDistance (σ ε n) (groupedPower ρ n) ≤ ε) :
    IidLowerLimit (conditionalEntropy ρ)
        (fun ε n => ((((n : ℝ)⁻¹ * condEntropySub (σ ε n)) : ℝ) : EReal)) ∧
      IidUpperLimit (conditionalEntropy ρ)
        (fun ε n => ((((n : ℝ)⁻¹ * condEntropySub (σ ε n)) : ℝ) : EReal)) := by sorry

end IntuitiveDPI.Smooth
