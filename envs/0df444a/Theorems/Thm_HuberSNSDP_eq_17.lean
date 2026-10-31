-- Prove2me | Theorems.Thm_HuberSNSDP_eq_17
-- name    : HuberSNSDP.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:22.664338+00:00
-- url     : https://prove2.me/theorems/dba31362-9af8-48c3-a21e-8058ac2744ce
-- title:
--   (17) — every $V_0\in\partial_B\Pi_{\mathbb S^n_+}(W)$ is $V(0,\cdot)$ for some $V\in\partial_B\Phi(0,W)$
-- statement:
--   Let $W\in\mathbb S^n$. For every $V_0\in\partial_B\Pi_{\mathbb S^n_+}(W)$ there is $V\in\partial_B\Phi(0,W)$ with
--   $$V_0(H)=V(0,H)\qquad\text{for all }H\in\mathbb S^n.\qquad(17)$$
--
--   This transfers the nonsingularity theory of $\partial\mathcal F$ (Theorem 1) to $\partial\hat{\mathcal E}$ in Proposition 2.
--
--   **Formalization Note** $\Pi_{\mathbb S^n_+}$ is the metric projector onto the positive semidefinite cone.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: $\Pi_{\mathbb S^n_+}$ → the published metric projector `metricProj (psdCone (Fin n))`; reason: the projection onto the closed convex cone $\mathbb S^n_+$, as defined on p.4
--   - encoding: $W$ with the spectral decomposition (7) → any $W$; reason: every symmetric matrix has a spectral decomposition, so the hypothesis excludes nothing
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, (17), p.11

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Display (17), p.11 (Liang, Sun & Toh, arXiv:2303.05825v4): for any `V₀ ∈ ∂_BΠ_{Sⁿ₊}(W)` there
exists `V ∈ ∂_BΦ(0, W)` such that `V₀(H) = V(0, H)` for all `H ∈ Sⁿ`.

**Formalization Note.** `Π_{Sⁿ₊}` is the published metric projector onto `psdCone`; the spectral
decomposition of `W` used on the page exists for every `W` and is not a hypothesis. -/
theorem eq_17 {n : ℕ} (W : SymMat (Fin n))
    (V₀ : SymMat (Fin n) →L[ℝ] SymMat (Fin n))
    (hV₀ : V₀ ∈ bJac (metricProj (psdCone (Fin n))) W) :
    ∃ V ∈ bJac (PhiPair (ι := Fin n)) (rsPt 0 W), ∀ H : SymMat (Fin n), V₀ H = V (rsPt 0 H) := by sorry

end HuberSNSDP
