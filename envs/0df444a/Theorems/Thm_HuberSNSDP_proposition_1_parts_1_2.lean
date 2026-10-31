-- Prove2me | Theorems.Thm_HuberSNSDP_proposition_1_parts_1_2
-- name    : HuberSNSDP.proposition_1_parts_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:27.260485+00:00
-- url     : https://prove2.me/theorems/ae455450-3a4a-43a2-a74a-5caac428daee
-- title:
--   Proposition 1 (parts 1–2) — $\Phi$ is $C^1$ at $(\epsilon,W)$ for $\epsilon\neq0$ with derivative (14), and locally Lipschitz
-- statement:
--   Let $W\in\mathbb S^n$ have the spectral decomposition $W=P\,\mathrm{diag}(d)P^T$ with $P$ orthogonal and $d_1\ge\dots\ge d_n$, and let $\Phi(\epsilon,W)=P\,\mathrm{diag}(h(\epsilon,d_i))P^T$ be the Huber smoothing of the projection onto $\mathbb S^n_+$. Then:
--
--   1. for every $\epsilon\neq0$, $\Phi$ is continuously differentiable at $(\epsilon,W)$ and, for all $(\tau,H)\in\mathbb R\times\mathbb S^n$,
--   $$\Phi'(\epsilon,W)(\tau,H)=P\big[\Omega(\epsilon,d)\circ(P^THP)+\tau\mathcal D(\epsilon,d)\big]P^T,\qquad(14)$$
--   where $\circ$ is the Hadamard product and $\Omega(\epsilon,d)$, $\mathcal D(\epsilon,d)$ are defined in (13);
--   2. $\Phi$ is locally Lipschitz continuous on $\mathbb R\times\mathbb S^n$.
--
--   This is the differential calculus of $\Phi$ away from $\epsilon=0$ used to form the Newton system (24).
--
--   **Formalization Note** $\Phi$ is regarded as a map on the Euclidean space $\mathbb R\times\mathbb S^n$; $\Phi'$ is its Fréchet derivative.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: $\Phi(\epsilon,W)=P\,\mathrm{diag}(h(\epsilon,d_i))P^T$ → `cfc (huber ε) W` on the pair space `WithLp 2 (ℝ × SymMat (Fin n))`; reason: the spectral definition is the continuous functional calculus of the continuous function $h(\epsilon,\cdot)$; the same map
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Proposition 1, parts 1–2, (14), p.10

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Proposition 1, parts 1–2, p.10 (Liang, Sun & Toh, arXiv:2303.05825v4).

Let `W ∈ Sⁿ` have the spectral decomposition (7), `W = P diag(d) Pᵀ`. Then:
1. for any `ε ≠ 0`, `Φ` is continuously differentiable at `(ε, W)`, and (14) holds:
   `Φ′(ε, W)(τ, H) = P [Ω(ε, d) ∘ (PᵀHP) + τ𝒟(ε, d)] Pᵀ` for all `(τ, H) ∈ ℝ × Sⁿ`;
2. `Φ` is locally Lipschitz continuous on `ℝ × Sⁿ`.

**Formalization Note.** `Φ` is `PhiPair` on `ℝ × Sⁿ = WithLp 2 (ℝ × SymMat (Fin n))`, `Φ′` its
`fderiv`; `∘` is the Hadamard product; `τ` here is a direction, not the algorithm's `τ`. -/
theorem proposition_1_parts_1_2 (n : ℕ) :
    (∀ (W : SymMat (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      IsSpectralDecomp W P d → ∀ ε : ℝ, ε ≠ 0 →
        ContDiffAt ℝ 1 (PhiPair (ι := Fin n)) (rsPt ε W) ∧
        ∀ (τ : ℝ) (H : SymMat (Fin n)),
          (fderiv ℝ (PhiPair (ι := Fin n)) (rsPt ε W) (rsPt τ H)).toMat =
            P * (Matrix.hadamard (OmegaMat ε d) (P.transpose * H.toMat * P) +
              τ • Matrix.diagonal (Dvec ε d)) * P.transpose) ∧
    LocallyLipschitz (PhiPair (ι := Fin n)) := by sorry

end HuberSNSDP
