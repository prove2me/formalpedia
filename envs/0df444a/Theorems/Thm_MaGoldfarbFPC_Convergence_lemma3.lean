-- Prove2me | Theorems.Thm_MaGoldfarbFPC_Convergence_lemma3
-- name    : MaGoldfarbFPC.Convergence.lemma3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:58.569975+00:00
-- url     : https://prove2.me/theorems/73d05094-3e24-4c2e-88a6-4a29b54e46b7
-- title:
--   Lemma 3 — given an optimal X*, X is optimal for (1.8) iff ‖S_ν(h(X)) − X*‖_F = ‖X − X*‖_F
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be linear, $b\in\mathbb R^p$, $\mu>0$, $\tau\in(0,2/\lambda_{\max}(A^\top A))$ and $\nu=\tau\mu$. Let $g(X)=\mathcal A^*(\mathcal A(X)-b)$, $h(X)=X-\tau g(X)$, and let $X^*$ be an optimal solution of problem (1.8), $\min_X\mu\|X\|_*+\tfrac12\|\mathcal A(X)-b\|_2^2$. Then a matrix $X$ is also an optimal solution of (1.8) if and only if
--   $$\|S_\nu(h(X))-X^*\|_F=\|X-X^*\|_F. \tag{3.5}$$
--
--   The paper writes the left side also as $\|S_\nu(h(X))-S_\nu(h(X^*))\|_F$; the two agree because $S_\nu(h(X^*))=X^*$ by Corollary 1. The lemma identifies the optimal solutions as exactly the points that one step of the iteration does not move closer to $X^*$, which is how a limit point of the iterates is shown to be optimal.
--
--   **Formalization Note** $S_\nu(h(X))$ is a matrix $Z$ with `IsShrink (τ * μ) (h τ Aop b X) Z`. The paper's "$\equiv$" in (3.5) is the identity $S_\nu(h(X^*))=X^*$ (Corollary 1), not a second condition, so only the form with $X^*$ is stated. The step range is `StepRange τ Aop` ($0<\tau$, $\tau\|\mathcal A\|_2^2<2$), and $\mu>0$ is explicit. The optimality of $X^*$ is a hypothesis, as on the page ("Let $X^*$ be an optimal solution").
-- source:
--   Ma, Goldfarb and Chen, Fixed point and Bregman iterative methods for matrix rank minimization, arXiv:0905.1643v2, p. 11, Lemma 3, (3.5)

import Mathlib
import Definitions.Def_MaGoldfarbFPC_Convergence_Basic

namespace MaGoldfarbFPC.Convergence

open CaiCandesShen.Convergence

/-- Lemma 3, p. 11: let `X*` be an optimal solution of (1.8), `τ ∈ (0, 2/λ_max(AᵀA))` and
`ν = τμ`. Then `X` is also an optimal solution of (1.8) if and only if
`‖S_ν(h(X)) − X*‖_F = ‖X − X*‖_F`, (3.5). Here `Z = S_ν(h(X))`. -/
theorem lemma3 {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (μ τ : ℝ)
    (hμ : 0 < μ) (hτ : StepRange τ Aop) (Xs : Mat m n) (hXs : IsOptimal μ Aop b Xs)
    (X Z : Mat m n) (hZ : IsShrink (τ * μ) (h τ Aop b X) Z) :
    IsOptimal μ Aop b X ↔ frobNorm (Z - Xs) = frobNorm (X - Xs) := by sorry

end MaGoldfarbFPC.Convergence
