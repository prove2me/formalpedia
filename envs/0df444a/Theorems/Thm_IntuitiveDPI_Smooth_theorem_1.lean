-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_theorem_1
-- name    : IntuitiveDPI.Smooth.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:13.608419+00:00
-- url     : https://prove2.me/theorems/e8bdd616-2dca-4181-8a5d-28882f83eaed
-- title:
--   Theorem 1, p. 3 — smooth min-entropy DPI: H_min^ε(A|BC)_ρ ≤ H_min^ε(A|B)_ρ
-- statement:
--   Let $\rho=\rho_{ABC}$ be a density matrix on a finite-dimensional tripartite space $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_C$ and let $\rho_{AB}=\operatorname{Tr}_C\rho_{ABC}$. For every $\varepsilon$,
--   $$H^\varepsilon_{\min}(A|BC)_\rho\le H^\varepsilon_{\min}(A|B)_\rho,$$
--   where $H^\varepsilon_{\min}(A|B)_\rho=\max_{\rho'\in\mathcal B^\varepsilon(\rho_{AB})}H_{\min}(A|B)_{\rho'}$ is the smooth conditional min-entropy (3), and $H_{\min}(A|B)_\rho=\max\{\lambda : \exists\sigma_B\text{ density},\ \rho_{AB}\le2^{-\lambda}\mathbb 1_A\otimes\sigma_B\}$ is (2).
--
--   This is the data processing inequality for the smooth min-entropy: discarding the system $C$ from the conditioning cannot decrease uncertainty about $A$. Combined with the quantum asymptotic equipartition property (Theorem 2) it yields the data processing inequality for the von Neumann entropy (Theorem 3), the goal of this mission.
--
--   **Formalization Note** The conditioning system $BC$ is the type `B × C`, so $\rho$ lives on `A × (B × C)`; $\operatorname{Tr}_C$ is `marginalAB` of `Dependency50.P35`, and the smooth entropies are `smoothConditionalMinEntropy` of `Information100.P67` (values in `EReal`). No hypothesis on $\varepsilon$ is needed: for $\varepsilon<0$ both balls are empty and both sides are $-\infty$, and for $\varepsilon\ge1$ both balls contain $0$ and both sides are $+\infty$. Types are in `Type` because the reused `marginalAB` is stated there.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 3, Theorem 1, (4)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Theorem 1, (4), p. 3 (smooth min-entropy DPI): for a density matrix `ρ` on
`A ⊗ B ⊗ C`, `H^ε_min(A|BC)_ρ ≤ H^ε_min(A|B)_ρ`, where `ρ_AB = Tr_C ρ`. -/
theorem theorem_1 {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : IsDensityMatrix ρ) (ε : ℝ) :
    smoothConditionalMinEntropy ρ ε ≤ smoothConditionalMinEntropy (marginalAB ρ) ε := by sorry

end IntuitiveDPI.Smooth
