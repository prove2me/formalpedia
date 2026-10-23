-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_5_1
-- name    : IntuitiveDPI.Smooth.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:18.476522+00:00
-- url     : https://prove2.me/theorems/34c050e4-67d1-4285-8a10-d501aa6b56b9
-- title:
--   Lemma 5.1, p. 5 — chain rule: H_min^ε(AB)_ρ − H_0^ε(B)_ρ ≤ H_min^{3ε}(A|B)_ρ
-- statement:
--   Let $\rho=\rho_{AB}$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$ and $\rho_B=\operatorname{Tr}_A\rho_{AB}$. For every $\varepsilon$,
--   $$H^\varepsilon_{\min}(AB)_\rho-H^\varepsilon_0(B)_\rho\le H^{3\varepsilon}_{\min}(A|B)_\rho.$$
--   Here $H^\varepsilon_{\min}(AB)_\rho$ is the non-conditional smooth min-entropy of the whole system $AB$, $H^\varepsilon_0(B)_\rho=\min_{\rho'\in\mathcal B^\varepsilon(\rho_B)}\log\operatorname{rank}\rho'$ is the smooth 0th order Rényi entropy of the marginal, and the right-hand side is the conditional smooth min-entropy with smoothing parameter $3\varepsilon$.
--
--   The chain rule bounds the conditional smooth min-entropy from below by non-conditional smooth entropies, whose i.i.d. limits are computed in Lemmas 5.4 and 5.5; applied with $\varepsilon/3$ to $\rho^{\otimes n}$ it gives the lower half of the QAEP (Lemma 4.1).
--
--   **Formalization Note** The entropies take values in `EReal` and the difference is `EReal` subtraction. The statement is asserted for every real $\varepsilon$ because the degenerate ranges hold by the conventions: for $\varepsilon<0$ the left side is $-\infty-(+\infty)=-\infty$; for $\varepsilon\ge1/3$ the ball $\mathcal B^{3\varepsilon}(\rho)$ contains $0$ and the right side is $+\infty$. The constant $3$ is the paper's.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 5, Lemma 5.1, (14)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma 5.1, (14), p. 5 (chain rule): for a density matrix `ρ` on `A ⊗ B`,
`H^ε_min(AB)_ρ - H^ε_0(B)_ρ ≤ H^{3ε}_min(A|B)_ρ`, with `ρ_B = Tr_A ρ`. -/
theorem lemma_5_1 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (ε : ℝ) :
    smoothMinEntropy ρ ε - smoothZeroEntropy (traceLeft ρ) ε ≤
      smoothConditionalMinEntropy ρ (3 * ε) := by sorry

end IntuitiveDPI.Smooth
